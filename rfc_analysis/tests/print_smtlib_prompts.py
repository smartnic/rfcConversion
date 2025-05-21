import sys
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.generators.smtlib_generator import SMTLIBGenerator
import json
import logging
from datetime import datetime
from typing import List, Dict, Any

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('smtlib_generation.log'),
        logging.StreamHandler()
    ]
)

def process_statement(statement: str, generator: SMTLIBGenerator) -> Dict[str, Any]:
    """Process a single statement and return the results."""
    try:
        logging.info(f"Processing statement: {statement}")
        
        # Generate SMT-LIB conversion using local generator
        result = generator.generate_smtlib(statement)
        
        if 'error' in result:
            logging.error(f"Error generating SMT-LIB: {result['error']}")
            return {
                "statement": statement,
                "timestamp": datetime.now().isoformat(),
                "success": False,
                "error": result['error']
            }
        
        # Print the concise output
        print("\n" + "="*80)
        print(f"RFC Statement: {statement}")
        print("="*80)
        print("\nSMT-LIB Conversion:")
        print(result['smtlib_conversion'])
        print("\nPredicates Used:")
        for pred in result['predicates_used']:
            print(f"- {pred}")
        print("\nExplanation:")
        print(result['explanation'])
        print("="*80 + "\n")
        
        return {
            "statement": statement,
            "timestamp": datetime.now().isoformat(),
            "success": True,
            "smtlib_conversion": result['smtlib_conversion'],
            "predicates_used": result['predicates_used'],
            "explanation": result['explanation']
        }
        
    except Exception as e:
        logging.error(f"Error processing statement: {str(e)}")
        return {
            "statement": statement,
            "timestamp": datetime.now().isoformat(),
            "success": False,
            "error": str(e)
        }

def main():
    # Get the current working directory
    cwd = os.getcwd()
    logging.info(f"Current working directory: {cwd}")
    
    # Create output directory if it doesn't exist
    output_dir = os.path.join(cwd, "output")
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    
    # RFC statements to process
    statements = [
        "A TCP segment has a sequence number.",
        "A SYN segment has a SYN flag.",
        "An ACK segment has an ACK flag.",
        "A TCP endpoint has a state.",
        "A TCP endpoint has a window size.",
        "A TCP segment has a source port.",
        "A TCP segment has a destination port.",
        "A TCP endpoint has a socket."
    ]
    
    # Initialize SMT-LIB generator
    generator = SMTLIBGenerator()
    
    try:
        # Process statements and collect results
        results = []
        for statement in statements:
            result = process_statement(statement, generator)
            results.append(result)
        
        # Save results
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        output_file = os.path.join(output_dir, f"smtlib_results_{timestamp}.json")
        
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

if __name__ == "__main__":
    main() 