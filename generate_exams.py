# /// script
# requires-python = ">=3.11"
# dependencies = [
#     "weasyprint",
#     "Mako",
#     "lxml",
# ]
# ///

import os
import sys
import argparse
import zipfile
import tempfile
import re
import html
import copy
import urllib.parse
import base64
import mimetypes
from pathlib import Path
from random import shuffle
from os.path import splitext, basename, join, dirname, abspath
from lxml import etree  # type: ignore
from mako.template import Template
from weasyprint import HTML

# --- Question Data Classes ---
class BaseQuestion:
    def __init__(self):
        self.text = ""

class Essay(BaseQuestion):
    type = "essay"

class MultipleChoice(BaseQuestion):
    type = "multiple_choice"
    def __init__(self):
        super().__init__()
        self.answers = []

class TrueFalse(BaseQuestion):
    type = "true_false"

class Matching(BaseQuestion):
    type = "matching"
    def __init__(self):
        super().__init__()
        self.matches_1 = []
        self.matches_2 = []

# --- HTML Extraction & Cleanup ---
def get_inner_html(node, base_dir=None):
    """Safely extracts inner HTML text, cleaning up Canvas QTI artifacts and embedding images as Base64."""
    if node is None:
        return ""
        
    text = ""
    # QTI 1.2 stores HTML inside <mattext>
    if node.tag.endswith('mattext'):
        text = node.text or ""
    elif node.tag.endswith('material'):
        # Dive into the <material> tag to find <mattext>
        mattext = node.xpath('.//*[local-name()="mattext"]')
        if mattext:
            text = mattext[0].text or ""
        else:
            text = node.text or ""
    else:
        # QTI 2.1: Content is embedded XML
        node_copy = copy.deepcopy(node)
        
        # Clean up QTI Interaction tags to prevent fallback text insertion
        for interaction in node_copy.xpath('.//*[contains(local-name(), "Interaction")]'):
            prompt = interaction.xpath('.//*[local-name()="prompt"]')
            if prompt:
                interaction.getparent().replace(interaction, prompt[0])
            else:
                interaction.getparent().remove(interaction)
                
        text = node_copy.text or ""
        for child in node_copy:
            text += etree.tostring(child, encoding='unicode')
            
    # Canvas frequently double or triple escapes HTML in XML exports.
    for _ in range(3):
        if '&lt;' in text or '&amp;' in text or '&gt;' in text:
            text = html.unescape(text)
            
    # Clean up Canvas specific base variables for images
    text = text.replace('%24IMS-CC-FILEBASE%24/../', '')
    text = text.replace('%24IMS-CC-FILEBASE%24/', '')
    text = text.replace('$IMS-CC-FILEBASE$/../', '')
    text = text.replace('$IMS-CC-FILEBASE$/', '')
    
    # Strip URL query parameters from image sources
    text = re.sub(r'(src="[^"?]+)\?[^"]+(")', r'\1\2', text)
    
    # Inject Base64 Image Data
    if base_dir:
        def inject_base64(match):
            original_src = match.group(1)
            decoded_src = urllib.parse.unquote(original_src)
            
            # Check direct path relative to temp_dir
            img_path = os.path.join(base_dir, decoded_src)
            
            # If not found, recursively search the temp_dir for the filename
            if not os.path.exists(img_path):
                filename = os.path.basename(decoded_src)
                for root, _, files in os.walk(base_dir):
                    if filename in files:
                        img_path = os.path.join(root, filename)
                        break
                        
            # If the image was successfully located on disk, base64 encode it
            if os.path.exists(img_path):
                mime_type, _ = mimetypes.guess_type(img_path)
                if not mime_type:
                    mime_type = 'image/png'  # safe fallback
                try:
                    with open(img_path, 'rb') as f:
                        b64_data = base64.b64encode(f.read()).decode('utf-8')
                    return f'src="data:{mime_type};base64,{b64_data}"'
                except Exception:
                    pass
                    
            # Fallback to URL encoded path if missing
            return f'src="{urllib.parse.quote(original_src)}"'

        text = re.sub(r'src="([^"]+)"', inject_base64, text)
        
    # Force HTML width/height attributes into inline CSS styles for WeasyPrint
    def force_image_styles(match):
        img_tag = match.group(0)
        width_match = re.search(r'width="(\d+)(px)?"', img_tag)
        height_match = re.search(r'height="(\d+)(px)?"', img_tag)
        
        style_str = ""
        if width_match:
            style_str += f"width: {width_match.group(1)}px; "
        if height_match:
            style_str += f"height: {height_match.group(1)}px; "
            
        if style_str:
            if 'style="' in img_tag:
                img_tag = re.sub(r'style="([^"]*)"', f'style="\\1 {style_str}"', img_tag)
            else:
                img_tag = img_tag.replace('<img ', f'<img style="{style_str}" ')
        return img_tag

    text = re.sub(r'<img [^>]+>', force_image_styles, text)
    
    # Remove Canvas injected UUID brackets (e.g., [927ccb22-7890-46e5...])
    text = re.sub(r'\[[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}\]', '', text)
    
    # Scrub literal manual grading fallback text
    text = text.replace('1. [Requires Manual Grading]', '')
    text = text.replace('[Requires Manual Grading]', '')
    
    # Remove empty namespace definitions that might have been serialized
    text = re.sub(r' xmlns="[^"]+"', '', text)
    
    return text.strip()

# --- Parsers ---
def parse_qti_xml(xml_path, base_dir=None):
    """Attempts to parse an XML file looking for QTI items using namespace-agnostic XPath."""
    question_list = []
    try:
        tree = etree.parse(xml_path)
        root = tree.getroot()
        
        # Check for QTI 2.1 format (<assessmentItem>) or QTI 1.2 (<item>)
        if 'assessmentItem' in root.tag:
            questions = [root]
        elif 'questestinterop' in root.tag:
            questions = root.xpath('.//*[local-name()="item"]')
        else:
            return []

        for item in questions:
            q_type = "unknown"
            
            # 1. Check for explicit Canvas metadata type mapping
            canvas_qtype_elems = item.xpath('.//*[local-name()="fieldlabel"][text()="question_type"]/following-sibling::*[local-name()="fieldentry"]')
            if canvas_qtype_elems:
                canvas_qtype = canvas_qtype_elems[0].text
                if canvas_qtype in ['essay_question', 'short_answer_question', 'text_only_question', 'fill_in_multiple_blanks_question', 'file_upload_question']:
                    q_type = "essay"
                elif canvas_qtype in ['multiple_choice_question', 'true_false_question', 'multiple_answers_question']:
                    q_type = "multiple_choice"
                elif canvas_qtype == 'matching_question':
                    q_type = "matching"

            # 2. Fallback to structural heuristics for standard/non-Canvas QTI
            if q_type == "unknown":
                if item.xpath('.//*[local-name()="extendedTextInteraction" or local-name()="render_fib"]'):
                    q_type = "essay"
                elif item.xpath('.//*[local-name()="matchInteraction"]') or item.get('ident', '').startswith('M_'):
                    q_type = "matching"
                elif item.xpath('.//*[local-name()="choiceInteraction" or local-name()="render_choice"]'):
                    q_type = "multiple_choice" 

            # Extract Question Content
            if q_type == "essay":
                q = Essay()
                body_elems = item.xpath('.//*[local-name()="itemBody"] | .//*[local-name()="presentation"]/*[local-name()="material"]')
                if body_elems:
                    q.text = get_inner_html(body_elems[0], base_dir)
                    if q.text: question_list.append(q)

            elif q_type == "multiple_choice":
                q = MultipleChoice()
                body_elems = item.xpath('.//*[local-name()="itemBody"] | .//*[local-name()="presentation"]/*[local-name()="material"]')
                if body_elems:
                    q.text = get_inner_html(body_elems[0], base_dir)
                
                choices = item.xpath('.//*[local-name()="simpleChoice"] | .//*[local-name()="response_label"]/*[local-name()="material"]')
                for c in choices:
                    ans_text = get_inner_html(c, base_dir)
                    if ans_text:
                        q.answers.append(ans_text)
                
                if len(q.answers) == 2 and all(a.strip().lower() in ['true', 'false'] for a in q.answers):
                    tf = TrueFalse()
                    tf.text = q.text
                    question_list.append(tf)
                elif q.text and q.answers:
                    question_list.append(q)

            elif q_type == "matching":
                q = Matching()
                body_elems = item.xpath('.//*[local-name()="itemBody"] | .//*[local-name()="presentation"]/*[local-name()="material"]')
                if body_elems:
                    q.text = get_inner_html(body_elems[0], base_dir)
                
                match_sets = item.xpath('.//*[local-name()="simpleMatchSet"]')
                if len(match_sets) >= 2:
                    for c in match_sets[0].xpath('.//*[local-name()="simpleAssociableChoice"]'):
                        q.matches_1.append(get_inner_html(c, base_dir))
                    for c in match_sets[1].xpath('.//*[local-name()="simpleAssociableChoice"]'):
                        q.matches_2.append(get_inner_html(c, base_dir))
                
                if q.text and q.matches_1:
                    question_list.append(q)
                    
    except Exception:
        pass
        
    return question_list

# --- Mako Template ---
HTML_TEMPLATE = """
<%
letters = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
%>
<!DOCTYPE html>
<html>
  <head>
    <meta charset="utf-8">
    <title>${title}</title>
    <style>
      @page { margin: 0.5in; }
      
      body { 
          font-family: "Times New Roman", Times, serif; 
          font-size: 11pt; 
          line-height: 1.25; 
      }
      
      .header-name { 
          text-align: right; 
          margin-bottom: 20px; 
          font-weight: bold;
          font-size: 11pt;
      }
      
      .title-page { page-break-after: always; text-align: center; margin-top: 80px; }
      .page-break { page-break-after: always; }
      
      .question-block { 
          page-break-inside: avoid; 
          margin-bottom: 18px; 
      }
      
      /* Collapse margins on paragraphs inside questions */
      .question-text p {
          margin-top: 0;
          margin-bottom: 4px;
      }
      
      .question-text p:last-child {
          margin-bottom: 0;
      }

      /* Compact Multiple Choice List Formatting */
      ol.mc-answers { 
          list-style-type: upper-alpha; 
          margin-top: 6px; 
          margin-bottom: 0;
          padding-left: 25px;
      }
      
      ol.mc-answers li { 
          margin-bottom: 4px; 
          padding-left: 2px;
      }
      
      /* Force Canvas's injected paragraph tags inside options to stay inline */
      ol.mc-answers li > p {
          display: inline;
          margin: 0;
      }

      /* Allow images to flow inline without breaking text, and respect HTML dimensions */
      img { 
          max-width: 100%; 
          display: inline-block; 
          vertical-align: middle; 
      }
      
      table { width: 100%; border-collapse: collapse; margin-top: 8px; }
      th, td { text-align: left; padding: 4px 6px; vertical-align: top; }
    </style>
  </head>
  <body>
    <div class="header-name">
        Name:_______________________________________________________
    </div>
            
    <div class="title-page">
        <h1>${title}</h1>
        % if closed_book:
            <h2>This exam is closed book and closed note</h2>
        % endif
        % if calc_allowed:
            <h2>A calculator may be used</h2>
        % else:
            <h2>No calculators or other electronic devices may be used</h2>
        % endif
        <h2>All questions are one point unless noted otherwise</h2>
        <h2>${len(question_list)} questions total</h2>
    </div>
   
    % if double_sided:
        <div class="page-break"></div>
    % endif
    
    <div class="header-name">
        Name:_______________________________________________________
    </div>
    
    <ol>
    % for question in question_list:
        <div class="question-block">
        % if question.type == "essay":
            <li>
                <div class="question-text">${question.text | n}</div>
                <br><br><br><br>
            </li>
            
        % elif question.type == "multiple_choice":
            <li>
                <div class="question-text">${question.text | n}</div>
                <ol class="mc-answers">
                    % for answer in question.answers:
                        <li>${answer | n}</li>
                    % endfor 
                </ol>
            </li>
            
        % elif question.type == "matching":
            <li>
                <div class="question-text">${question.text | n}</div>
                <table>
                    <tr>
                        <th>Questions/Definitions</th> 
                        <th>Responses</th>
                    </tr>
                    % for num, match in enumerate(question.matches_2):
                        % if num < len(question.matches_1):
                            <tr>
                                <td>___${num+1}.  ${question.matches_1[num] | n}</td>
                                <td>${letters[num]}.  ${match | n}</td>
                            </tr>
                        % else:
                            <tr>
                                <td></td>
                                <td>${letters[num]}.  ${match | n}</td>
                            </tr>                            
                        % endif
                    % endfor 
                </table>
            </li>
    
        % elif question.type == "true_false":
            <li>
                <div class="question-text">${question.text | n}</div>
                <ol class="mc-answers">
                        <li>True</li>
                        <li>False</li>
                </ol>
            </li>
        % endif 
        </div>
    % endfor
    </ol>
  </body>
</html>
"""

def main():
    parser = argparse.ArgumentParser(description="Generate Randomized Exam PDFs from Canvas QTI Exports.")
    parser.add_argument("zip_file", help="Path to the input Canvas QTI .zip file")
    parser.add_argument("--title", default="ME 5365 Final Exam, Spring 2026", help="Exam Title")
    parser.add_argument("--num-exams", type=int, default=1, help="Number of randomized exams to generate")
    
    parser.add_argument("--calc-allowed", action="store_true", help="Allow calculators (Default: False)")
    parser.add_argument("--open-book", dest="closed_book", action="store_false", help="Exam is Open Book (Default: Closed)")
    parser.add_argument("--no-shuffle", dest="shuffle_questions", action="store_false", help="Do not shuffle questions")
    parser.add_argument("--single-sided", dest="double_sided", action="store_false", help="Single sided printing layout")
    parser.add_argument("--debug", action="store_true", help="Save raw HTML file for debugging.")
    
    parser.set_defaults(calc_allowed=False, closed_book=True, shuffle_questions=True, double_sided=True)
    
    args = parser.parse_args()

    zip_path = abspath(args.zip_file)
    if not os.path.exists(zip_path):
        print(f"Error: Could not find file {zip_path}")
        sys.exit(1)

    target_dir = dirname(zip_path)
    base_name = splitext(basename(zip_path))[0]

    question_list = []
    print(f"Extracting '{basename(zip_path)}'...")
    
    with tempfile.TemporaryDirectory() as temp_dir:
        with zipfile.ZipFile(zip_path, 'r') as z:
            z.extractall(temp_dir)
            
        print("Parsing XML questions...")
        for root_dir, _, files in os.walk(temp_dir):
            for file in files:
                if file.endswith('.xml'):
                    questions = parse_qti_xml(join(root_dir, file), base_dir=temp_dir)
                    question_list.extend(questions)

        if not question_list:
            print("Error: Could not find any valid questions in the provided QTI zip.")
            sys.exit(1)
            
        print(f"Found {len(question_list)} questions. Generating {args.num_exams} PDF(s)...")

        mytemplate = Template(text=HTML_TEMPLATE)

        for i in range(args.num_exams):
            current_q_list = list(question_list) 
            
            if args.shuffle_questions:
                for question in current_q_list:
                    if question.type == "multiple_choice":
                        shuffle(question.answers)
                    elif question.type == "matching":
                        shuffle(question.matches_2) 
                shuffle(current_q_list)

            html_text = mytemplate.render(
                question_list=current_q_list,
                title=args.title,
                calc_allowed=args.calc_allowed,
                closed_book=args.closed_book,
                double_sided=args.double_sided
            )

            suffix = f"_{i+1}" if args.num_exams > 1 else ""
            pdf_filename = join(target_dir, f"{base_name}{suffix}.pdf")
            html_filename = join(target_dir, f"{base_name}{suffix}_debug.html")

            if args.debug:
                with open(html_filename, 'w', encoding='utf-8') as f:
                    f.write(str(html_text))
                print(f"Debug HTML saved to: {html_filename}")

            html_doc = HTML(string=html_text)
            html_doc.write_pdf(pdf_filename)
            
            print(f"Saved PDF to: {pdf_filename}")

    print("Done!")

if __name__ == "__main__":
    main()