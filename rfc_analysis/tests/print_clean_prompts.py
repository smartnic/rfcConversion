import sys
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.prompts.tcp_rfc_prompt import get_tcp_rfc_prompt
import requests
import json
import time
import logging
from datetime import datetime
import re
from typing import Tuple, List, Dict, Any

# Set Hugging Face API token
HF_API_TOKEN = "key"  # Replace with your actual token

# RFC statements to test
RFC_STATEMENTS = [
    {
        'id': 1,
        'statement': 'A TCP segment has a sequence number.'
    },
    {
        'id': 2,
        'statement': 'A SYN segment has a SYN flag.'
    },
    {
        'id': 3,
        'statement': 'An ACK segment has an ACK flag.'
    },
    {
        'id': 4,
        'statement': 'A TCP endpoint has a state.'
    },
    {
        'id': 5,
        'statement': 'A TCP endpoint has a window size.'
    },
    {
        'id': 6,
        'statement': 'A TCP segment has a source port.'
    },
    {
        'id': 7,
        'statement': 'A TCP segment has a destination port.'
    },
    {
        'id': 8,
        'statement': 'A TCP endpoint has a socket.'
    }
]

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('fol_generation.log'),
        logging.StreamHandler()
    ]
)

def generate_fol_conversion(prompt, max_retries=3):
    """Generate FOL conversion using Hugging Face's Inference API with Mixtral-8x7B"""
    for attempt in range(max_retries):
        try:
            API_URL = "https://api-inference.huggingface.co/models/mistralai/Mixtral-8x7B-Instruct-v0.1"
            headers = {"Authorization": f"Bearer {HF_API_TOKEN}"}
            
            # Format the prompt for Mixtral's instruction format
            formatted_prompt = (
                "<s>[INST] Convert this TCP requirement to First-Order Logic (FOL). You MUST provide:\n"
                "1. The FOL expression using the predicates from the prompt\n"
                "2. A brief explanation\n\n"
                "Requirements for FOL format:\n"
                "- Use standard FOL symbols: ∀, ∃, ∧, ∨, →, ¬\n"
                "- Do not use LaTeX notation or \\text{} commands\n"
                "- Use simple predicate names like is_tcp_endpoint(x), has_flag(m, f)\n"
                "- Separate complex expressions with parentheses\n"
                "- Use indentation for long expressions\n"
                "- Use underscore for multi-word predicates\n\n"
                "TCP Protocol Elements and Predicates:\n" +
                get_tcp_rfc_prompt().split("# Task")[0].strip() + "\n\n"
                f"Requirement to convert: {prompt}\n\n"
                "You MUST provide both the FOL expression and explanation. Do not skip either part.\n"
                "Start with 'FOL:' followed by your expression, then 'Explanation:' followed by your explanation. [/INST]"
            )
            
            logging.info(f"Sending prompt for statement: {prompt}")
            
            payload = {
                "inputs": formatted_prompt,
                "parameters": {
                    "max_new_tokens": 1000,
                    "temperature": 0.2,
                    "return_full_text": False,
                    "do_sample": True,
                    "top_p": 0.9,
                    "top_k": 40,
                    "repetition_penalty": 1.2
                }
            }
            
            print(f"Sending request to Mixtral-8x7B (attempt {attempt + 1}/{max_retries})...")
            response = requests.post(API_URL, headers=headers, json=payload)
            
            # Check if we need to wait for the model to load
            if response.status_code == 503:
                print("Model is loading, waiting...")
                time.sleep(20)  # Wait 20 seconds before retry
                continue
            
            response.raise_for_status()
            
            result = response.json()
            print(f"Received response from Mixtral-8x7B")
            
            # Clean up the response
            generated_text = result[0]["generated_text"].strip()
            logging.info(f"Raw response: {generated_text}")
            
            if generated_text.startswith("Here is") or generated_text.startswith("The FOL"):
                # Remove common prefixes
                lines = generated_text.split("\n")
                generated_text = "\n".join(line for line in lines if line.strip())
            
            # Clean up LaTeX notation if present
            generated_text = (generated_text
                .replace(r'\[', '')
                .replace(r'\]', '')
                .replace(r'\text{', '')
                .replace('}', '')
                .replace(r'\land', '∧')
                .replace(r'\lor', '∨')
                .replace(r'\rightarrow', '→')
                .replace(r'\neg', '¬')
                .replace(r'\forall', '∀')
                .replace(r'\exists', '∃')
                .replace('\\', '')
            )
            
            # Enhanced response validation
            if not generated_text:
                logging.warning(f"Empty response received on attempt {attempt + 1}")
                continue
                
            if "FOL:" not in generated_text:
                logging.warning(f"Response missing FOL section on attempt {attempt + 1}")
                continue
                
            if "Explanation:" not in generated_text:
                logging.warning(f"Response missing Explanation section on attempt {attempt + 1}")
                continue
            
            # Extract FOL and explanation
            fol_part = ""
            explanation_part = ""
            
            parts = generated_text.split("Explanation:", 1)
            if len(parts) == 2:
                fol_part = parts[0].replace("FOL:", "").strip()
                explanation_part = parts[1].strip()
                
                if not fol_part or not explanation_part:
                    logging.warning(f"Empty FOL or explanation section on attempt {attempt + 1}")
                    continue
                    
                # Construct properly formatted response
                formatted_response = f"FOL:\n{fol_part}\n\nExplanation:\n{explanation_part}"
                return formatted_response
            
            logging.warning(f"Incomplete response structure on attempt {attempt + 1}")
            continue
            
        except requests.exceptions.HTTPError as e:
            logging.error(f"HTTP Error on attempt {attempt + 1}: {e}")
            logging.error(f"Response: {e.response.text if hasattr(e, 'response') else 'No response text'}")
            if attempt == max_retries - 1:
                return f"HTTP Error after {max_retries} attempts: {str(e)}"
        except Exception as e:
            logging.error(f"Unexpected Error on attempt {attempt + 1}: {e}")
            if attempt == max_retries - 1:
                return f"Error after {max_retries} attempts: {str(e)}"
        
        # Wait before retrying
        if attempt < max_retries - 1:
            time.sleep(5)
    
    return "Failed to generate complete response after all retries."

def is_response_complete(response):
    """Check if the response contains both FOL and explanation."""
    if not response or not isinstance(response, str):
        return False
    
    # Check for FOL indicators
    fol_indicators = ['∀', '∃', '→', '∧', '∨', '¬']
    has_fol = any(indicator in response for indicator in fol_indicators)
    
    # Check for explanation indicators
    explanation_indicators = ['explanation:', 'this means:', 'where:', 'because:']
    has_explanation = any(indicator.lower() in response.lower() for indicator in explanation_indicators)
    
    # Check for minimum length and structure
    is_long_enough = len(response.strip()) > 50
    has_structure = '\n' in response  # Expecting some formatting
    
    return has_fol and has_explanation and is_long_enough and has_structure

def generate_concise_output():
    """Generate concise output for each RFC statement"""
    output = []
    base_prompt = get_tcp_rfc_prompt()
    
    # Clear files at start
    open("generated_fol.txt", "w").close()
    open("failed_generations.txt", "w").close()
    
    for statement in RFC_STATEMENTS:
        logging.info(f"\nProcessing statement {statement['id']}...")
        
        # Replace the placeholder in the prompt with the current statement
        current_prompt = base_prompt.replace("[TCP Requirement]", statement['statement'])
        
        # Generate FOL conversion with improved retry mechanism
        fol_output = generate_fol_with_retries(current_prompt)
        
        # Save results to appropriate files
        save_results(statement['statement'], fol_output, "generated_fol.txt", "failed_generations.txt")
        
        # Add to in-memory output
        output.append("\n" + "="*80)
        output.append(f"RFC Statement {statement['id']}:")
        output.append(f"\"{statement['statement']}\"")
        output.append("="*80)
        if fol_output:
            output.append(fol_output)
        else:
            output.append("Failed to generate complete response after all retries.")
        output.append("\n" + "="*80 + "\n")
    
    return '\n'.join(output)

def write_output_to_file(output_text, filename='generated_fol.txt'):
    """Write the output to a file"""
    with open(filename, 'w', encoding='utf-8') as f:
        f.write(output_text)

def print_concise_prompts():
    """Generate concise prompts and write them to a file"""
    print("Starting FOL generation process...")
    output = generate_concise_output()
    write_output_to_file(output)
    print(f"Generated FOL output has been written to generated_fol.txt")

def generate_fol_with_retries(prompt, max_retries=5, delay_between_retries=2):
    """Generate FOL with retries on incomplete responses."""
    for attempt in range(max_retries):
        try:
            logging.info(f"Attempt {attempt + 1}/{max_retries} to generate FOL")
            response = generate_fol_conversion(prompt)
            
            if is_response_complete(response):
                logging.info("Generated complete response")
                return response, True
            
            logging.warning(f"Incomplete response on attempt {attempt + 1}")
            if attempt < max_retries - 1:  # Only delay if we have more retries
                time.sleep(delay_between_retries)
                
        except Exception as e:
            logging.error(f"Error during generation: {str(e)}")
            if attempt < max_retries - 1:
                time.sleep(delay_between_retries)
    
    logging.error("Failed to generate complete response after all retries")
    return response, False  # Return last response with failure flag

def save_results(statement, response, output_file, failed_file):
    """Save results to appropriate files with timestamps."""
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    
    # Use absolute paths for output files
    output_file = os.path.join(os.getcwd(), output_file)
    failed_file = os.path.join(os.getcwd(), failed_file)
    
    if is_response_complete(response):
        with open(output_file, 'a', encoding='utf-8') as f:
            f.write(f"\n{'='*80}\n")
            f.write(f"Timestamp: {timestamp}\n")
            f.write(f"Statement:\n{statement}\n\n")
            f.write(f"Response:\n{response}\n")
    else:
        with open(failed_file, 'a', encoding='utf-8') as f:
            f.write(f"\n{'='*80}\n")
            f.write(f"Timestamp: {timestamp}\n")
            f.write(f"Statement:\n{statement}\n\n")
            f.write(f"Incomplete Response:\n{response}\n")

def process_statement(statement: str, section_titles: List[str]) -> Dict[str, Any]:
    """Process a single statement and return the results.
    
    Args:
        statement: The RFC statement to process
        section_titles: List of section titles for the prompt
        
    Returns:
        Dictionary containing processing results and metadata
    """
    try:
        logging.info(f"Processing statement: {statement}")
        
        # Generate FOL conversion using the API
        fol_output = generate_fol_conversion(statement)
        
        # Extract FOL expression and explanation
        fol_conversion = ""
        explanation = ""
        predicates = []
        
        if fol_output:
            # Split the output into lines
            lines = fol_output.split('\n')
            
            # Find FOL expression (usually the first line with ∀ or ∃)
            for line in lines:
                if '∀' in line or '∃' in line:
                    fol_conversion = line.strip()
                    # Extract predicates from the FOL expression
                    predicates = re.findall(r'[a-z_]+\([^)]*\)', fol_conversion)
                    break
            
            # Find explanation (usually after "Explanation:" or similar)
            for i, line in enumerate(lines):
                if 'explanation' in line.lower() or 'means' in line.lower():
                    explanation = '\n'.join(lines[i+1:]).strip()
                    break
        
        # Print the concise output
        print("\n" + "="*80)
        print(f"RFC Statement: {statement}")
        print("="*80)
        print("\nFOL Conversion:")
        print(fol_conversion)
        print("\nPredicates Used:")
        for pred in predicates:
            print(f"- {pred}")
        print("\nExplanation:")
        print(explanation)
        print("="*80 + "\n")
            
        return {
            "statement": statement,
            "timestamp": datetime.now().isoformat(),
            "success": True,
            "fol_conversion": fol_conversion,
            "predicates_used": predicates,
            "explanation": explanation
        }
        
    except Exception as e:
        logging.error(f"Error processing statement: {str(e)}")
        return {
            "statement": statement,
            "timestamp": datetime.now().isoformat(),
            "success": False,
            "error": str(e)
        }

def get_prompt_sections(statement: str) -> List[str]:
    """Get the prompt sections for a given RFC statement.
    
    Args:
        statement: The RFC statement to process
        
    Returns:
        List of prompt sections
    """
    # Get the base prompt
    base_prompt = get_tcp_rfc_prompt()
    
    # Replace the placeholder with the current statement
    full_prompt = base_prompt.replace("[TCP Requirement]", statement)
    
    # Split the prompt into sections based on headers
    sections = []
    current_section = []
    
    # Split by double newlines first to handle potential section breaks
    paragraphs = full_prompt.split('\n\n')
    
    for para in paragraphs:
        lines = para.split('\n')
        for line in lines:
            line = line.strip()
            if not line:
                continue
                
            # Check if this is a section header (## or ###)
            if line.startswith('# '):
                if current_section:
                    sections.append('\n'.join(current_section))
                    current_section = []
                current_section.append(line)
            else:
                current_section.append(line)
                
    # Add the last section if it exists
    if current_section:
        sections.append('\n'.join(current_section))
        
    # Ensure we have exactly 8 sections
    if len(sections) != 8:
        # If we have fewer sections, pad with empty sections
        while len(sections) < 8:
            sections.append("")
        # If we have more sections, combine extra sections into the last one
        if len(sections) > 8:
            sections[7] = '\n'.join(sections[7:])
            sections = sections[:8]
            
    return sections

if __name__ == "__main__":
    # Set up logging
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(message)s',
        handlers=[
            logging.FileHandler('debug.log'),
            logging.StreamHandler()
        ]
    )
    
    # Get the current working directory
    cwd = os.getcwd()
    logging.info(f"Current working directory: {cwd}")
    
    # Create output directory if it doesn't exist
    output_dir = os.path.join(cwd, "output")
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    
    # Section titles for prompt organization
    section_titles = [
        "Introduction",
        "Protocol Elements",
        "Predicate Categories", 
        "State Definitions",
        "Message Types",
        "Conversion Rules",
        "Example Conversions",
        "Task"
    ]
    
    try:
        # Load statements from JSON file
        statements_file = os.path.join(cwd, "rfc_analysis", "tests", "rfc_statements.json")
        logging.info(f"Looking for statements file at: {statements_file}")
        
        try:
            with open(statements_file, 'r') as f:
                data = json.load(f)
                statements = data["statements"]
                logging.info(f"Loaded {len(statements)} statements from rfc_statements.json")
        except FileNotFoundError:
            logging.warning(f"rfc_statements.json not found at {statements_file}, using example statements")
            statements = RFC_STATEMENTS
    
        # Process statements and collect results
        results = []
        for i, statement in enumerate(statements, 1):
            logging.info(f"Processing statement {i}/{len(statements)}")
            result = process_statement(statement, section_titles)
            results.append(result)
            
            # Add delay between statements
            if i < len(statements):
                time.sleep(1)  # 1 second delay
                
        # Save results
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        output_file = os.path.join(output_dir, f"results_{timestamp}.json")
        
        with open(output_file, 'w') as f:
            json.dump({
                "timestamp": datetime.now().isoformat(),
                "total_statements": len(statements),
                "successful": sum(1 for r in results if r["success"]),
                "results": results
            }, f, indent=2)
            
        logging.info(f"Results saved to {output_file}")
        
    except Exception as e:
        logging.error(f"Fatal error: {str(e)}")
        raise 