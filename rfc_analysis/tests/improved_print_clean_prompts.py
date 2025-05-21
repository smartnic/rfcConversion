import sys
import os
import requests
import json
import time
import logging
from datetime import datetime
import re
from typing import Tuple, List, Dict, Any, Optional
from dotenv import load_dotenv

# Add parent directory to path for imports
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# Import project-specific modules
from src.prompts.tcp_rfc_prompt import get_tcp_rfc_prompt

# Load environment variables from .env file if it exists
load_dotenv()

# Get API token from environment variable or use default (for testing only)
HF_API_TOKEN = os.getenv("HF_API_TOKEN", "")

# If no token in environment, warn user but provide fallback for testing
if not HF_API_TOKEN:
    logging.warning("No HF_API_TOKEN found in environment variables. Using default test token.")
    # This is just a placeholder - in production, users should set their own token
    HF_API_TOKEN = "key"

# Default RFC statements for testing
DEFAULT_RFC_STATEMENTS = [
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

# Model configuration
MODEL_CONFIG = {
    "url": "https://api-inference.huggingface.co/models/mistralai/Mixtral-8x7B-Instruct-v0.1",
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

# Section titles for prompt organization
SECTION_TITLES = [
    "Introduction",
    "Protocol Elements",
    "Predicate Categories", 
    "State Definitions",
    "Message Types",
    "Conversion Rules",
    "Example Conversions",
    "Task"
]


def setup_logging(log_file: str = 'fol_generation.log', debug_file: str = 'debug.log') -> None:
    """Set up logging configuration.
    
    Args:
        log_file: Path to the main log file
        debug_file: Path to the debug log file
    """
    # Create logs directory if it doesn't exist
    logs_dir = os.path.join(os.getcwd(), "logs")
    if not os.path.exists(logs_dir):
        os.makedirs(logs_dir)
    
    # Set up main logger
    log_path = os.path.join(logs_dir, log_file)
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(message)s',
        handlers=[
            logging.FileHandler(log_path),
            logging.StreamHandler()
        ]
    )
    logging.info(f"Logging initialized. Log file: {log_path}")


def format_prompt(statement: str) -> str:
    """Format the prompt for the model with the given statement.
    
    Args:
        statement: The RFC statement to convert to FOL
        
    Returns:
        Formatted prompt string
    """
    # Get the base prompt template
    base_prompt = get_tcp_rfc_prompt()
    
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
        base_prompt.split("# Task")[0].strip() + "\n\n"
        f"Requirement to convert: {statement}\n\n"
        "You MUST provide both the FOL expression and explanation. Do not skip either part.\n"
        "Start with 'FOL:' followed by your expression, then 'Explanation:' followed by your explanation. [/INST]"
    )
    
    return formatted_prompt


def call_huggingface_api(prompt: str, max_retries: int = 3, retry_delay: int = 5) -> Optional[str]:
    """Call the Hugging Face API with the given prompt.
    
    Args:
        prompt: The formatted prompt to send to the API
        max_retries: Maximum number of retry attempts
        retry_delay: Delay between retries in seconds
        
    Returns:
        Generated text or None if all retries failed
    """
    headers = {"Authorization": f"Bearer {HF_API_TOKEN}"}
    payload = {
        "inputs": prompt,
        "parameters": MODEL_CONFIG["parameters"]
    }
    
    for attempt in range(max_retries):
        try:
            logging.info(f"Sending request to Mixtral-8x7B (attempt {attempt + 1}/{max_retries})...")
            response = requests.post(MODEL_CONFIG["url"], headers=headers, json=payload, timeout=60)
            
            # Handle model loading delay
            if response.status_code == 503:
                logging.info("Model is loading, waiting...")
                time.sleep(20)  # Wait longer for model to load
                continue
                
            # Handle other HTTP errors
            response.raise_for_status()
            
            result = response.json()
            logging.info("Received response from Mixtral-8x7B")
            
            if isinstance(result, list) and len(result) > 0 and "generated_text" in result[0]:
                return result[0]["generated_text"].strip()
            else:
                logging.warning(f"Unexpected response format: {result}")
                
        except requests.exceptions.Timeout:
            logging.error(f"Request timed out on attempt {attempt + 1}")
        except requests.exceptions.HTTPError as e:
            logging.error(f"HTTP Error on attempt {attempt + 1}: {e}")
            if hasattr(e, 'response') and e.response:
                logging.error(f"Response: {e.response.text}")
        except requests.exceptions.RequestException as e:
            logging.error(f"Request Error on attempt {attempt + 1}: {e}")
        except Exception as e:
            logging.error(f"Unexpected Error on attempt {attempt + 1}: {e}")
            
        # Wait before retrying, unless it's the last attempt
        if attempt < max_retries - 1:
            time.sleep(retry_delay)
    
    return None


def clean_generated_text(text: str) -> str:
    """Clean up the generated text from the model.
    
    Args:
        text: Raw generated text from the model
        
    Returns:
        Cleaned text
    """
    if not text:
        return ""
        
    # Remove common prefixes
    if text.startswith("Here is") or text.startswith("The FOL"):
        lines = text.split("\n")
        text = "\n".join(line for line in lines if line.strip())
    
    # Clean up LaTeX notation if present
    text = (text
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
    
    return text


def extract_fol_parts(text: str) -> Tuple[str, str]:
    """Extract FOL expression and explanation from the generated text.
    
    Args:
        text: Cleaned generated text from the model
        
    Returns:
        Tuple of (FOL expression, explanation)
    """
    fol_part = ""
    explanation_part = ""
    
    if "FOL:" in text and "Explanation:" in text:
        parts = text.split("Explanation:", 1)
        if len(parts) == 2:
            fol_part = parts[0].replace("FOL:", "").strip()
            explanation_part = parts[1].strip()
    
    return fol_part, explanation_part


def is_response_complete(response: str) -> bool:
    """Check if the response contains both FOL and explanation.
    
    Args:
        response: The response to check
        
    Returns:
        True if the response is complete, False otherwise
    """
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


def generate_fol_conversion(statement: str, max_retries: int = 3) -> Tuple[str, bool]:
    """Generate FOL conversion for a given RFC statement.
    
    Args:
        statement: The RFC statement to convert
        max_retries: Maximum number of retry attempts
        
    Returns:
        Tuple of (formatted response, success flag)
    """
    # Format the prompt
    prompt = format_prompt(statement)
    logging.info(f"Sending prompt for statement: {statement}")
    
    # Call the API
    generated_text = call_huggingface_api(prompt, max_retries)
    if not generated_text:
        return "Failed to generate response after all retries.", False
    
    # Clean up the response
    cleaned_text = clean_generated_text(generated_text)
    logging.info(f"Raw response: {cleaned_text}")
    
    # Validate the response
    if not is_response_complete(cleaned_text):
        logging.warning("Response validation failed")
        return cleaned_text, False
    
    # Extract FOL and explanation
    fol_part, explanation_part = extract_fol_parts(cleaned_text)
    
    if not fol_part or not explanation_part:
        logging.warning("Failed to extract FOL or explanation parts")
        return cleaned_text, False
    
    # Construct properly formatted response
    formatted_response = f"FOL:\n{fol_part}\n\nExplanation:\n{explanation_part}"
    return formatted_response, True


def save_results(statement: str, response: str, success: bool) -> None:
    """Save results to appropriate files with timestamps.
    
    Args:
        statement: The RFC statement that was processed
        response: The generated response
        success: Whether the generation was successful
    """
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    
    # Create output directory if it doesn't exist
    output_dir = os.path.join(os.getcwd(), "output")
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    
    # Determine output file based on success
    file_path = os.path.join(
        output_dir, 
        "generated_fol.txt" if success else "failed_generations.txt"
    )
    
    with open(file_path, 'a', encoding='utf-8') as f:
        f.write(f"\n{'='*80}\n")
        f.write(f"Timestamp: {timestamp}\n")
        f.write(f"Statement:\n{statement}\n\n")
        f.write(f"Response:\n{response}\n")


def extract_predicates(fol_expression: str) -> List[str]:
    """Extract predicates from a FOL expression.
    
    Args:
        fol_expression: The FOL expression to extract predicates from
        
    Returns:
        List of predicates found in the expression
    """
    if not fol_expression:
        return []
        
    return re.findall(r'[a-z_]+\([^)]*\)', fol_expression)


def process_statement(statement: str) -> Dict[str, Any]:
    """Process a single statement and return the results.
    
    Args:
        statement: The RFC statement to process
        
    Returns:
        Dictionary containing processing results and metadata
    """
    try:
        logging.info(f"Processing statement: {statement}")
        
        # Generate FOL conversion
        fol_output, success = generate_fol_conversion(statement)
        
        # Save results
        save_results(statement, fol_output, success)
        
        if success:
            # Extract FOL expression and explanation
            fol_part, explanation_part = extract_fol_parts(fol_output)
            
            # Extract predicates from the FOL expression
            predicates = extract_predicates(fol_part)
            
            # Print the concise output
            print("\n" + "="*80)
            print(f"RFC Statement: {statement}")
            print("="*80)
            print("\nFOL Conversion:")
            print(fol_part)
            print("\nPredicates Used:")
            for pred in predicates:
                print(f"- {pred}")
            print("\nExplanation:")
            print(explanation_part)
            print("="*80 + "\n")
            
            return {
                "statement": statement,
                "timestamp": datetime.now().isoformat(),
                "success": True,
                "fol_conversion": fol_part,
                "predicates_used": predicates,
                "explanation": explanation_part
            }
        else:
            logging.warning(f"Failed to generate complete response for: {statement}")
            return {
                "statement": statement,
                "timestamp": datetime.now().isoformat(),
                "success": False,
                "error": "Failed to generate complete response"
            }
            
    except Exception as e:
        logging.error(f"Error processing statement: {str(e)}")
        return {
            "statement": statement,
            "timestamp": datetime.now().isoformat(),
            "success": False,
            "error": str(e)
        }


def load_statements() -> List[Dict[str, Any]]:
    """Load RFC statements from a JSON file or use defaults.
    
    Returns:
        List of RFC statements
    """
    cwd = os.getcwd()
    statements_file = os.path.join(cwd, "rfc_analysis", "tests", "rfc_statements.json")
    logging.info(f"Looking for statements file at: {statements_file}")
    
    try:
        with open(statements_file, 'r') as f:
            data = json.load(f)
            statements = data["statements"]
            logging.info(f"Loaded {len(statements)} statements from rfc_statements.json")
            return statements
    except FileNotFoundError:
        logging.warning(f"rfc_statements.json not found at {statements_file}, using default statements")
        return DEFAULT_RFC_STATEMENTS
    except json.JSONDecodeError as e:
        logging.error(f"Error parsing JSON file: {e}")
        return DEFAULT_RFC_STATEMENTS


def main() -> None:
    """Main function to run the FOL generation process."""
    # Set up logging
    setup_logging()
    
    try:
        # Get the current working directory
        cwd = os.getcwd()
        logging.info(f"Current working directory: {cwd}")
        
        # Create output directory if it doesn't exist
        output_dir = os.path.join(cwd, "output")
        if not os.path.exists(output_dir):
            os.makedirs(output_dir)
        
        # Load statements
        statements = load_statements()
        
        # Process statements and collect results
        results = []
        for i, statement in enumerate(statements, 1):
            statement_text = statement['statement'] if isinstance(statement, dict) else statement
            logging.info(f"Processing statement {i}/{len(statements)}")
            
            result = process_statement(statement_text)
            results.append(result)
            
            # Add delay between statements to avoid rate limiting
            if i < len(statements):
                time.sleep(1)  # 1 second delay
                
        # Save results to JSON file
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
        print(f"\nProcessing complete! Results saved to {output_file}")
        
    except Exception as e:
        logging.error(f"Fatal error: {str(e)}")
        raise


if __name__ == "__main__":
    main()