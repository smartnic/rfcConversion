import sys
import os
import json
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.generators.smtlib_generator import SMTLIBGenerator
from z3 import *
import logging
from datetime import datetime
from typing import Dict, Any, Tuple

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('z3_verification.log'),
        logging.StreamHandler()
    ]
)

class Z3Verifier:
    def __init__(self):
        self.solver = Solver()
        self.declarations = {}
        self.custom_sorts = {}
        
    def declare_custom_sort(self, sort_name: str):
        """Declare a custom sort if it doesn't exist."""
        if sort_name not in self.custom_sorts:
            self.custom_sorts[sort_name] = DeclareSort(sort_name)
        return self.custom_sorts[sort_name]
        
    def parse_smtlib(self, smtlib_str: str) -> Tuple[bool, str]:
        """Parse SMT-LIB string and add to Z3 solver."""
        try:
            # Clean up the SMT-LIB string
            smtlib_str = smtlib_str.replace('\n\n', '\n').strip()
            
            # First pass: collect all declarations
            declarations = []
            assertions = []
            current_expr = []
            
            for line in smtlib_str.split('\n'):
                line = line.strip()
                if not line:
                    continue
                    
                if line.startswith('('):
                    current_expr.append(line)
                    if line.count('(') == line.count(')'):
                        expr = ' '.join(current_expr)
                        if expr.startswith('(declare-'):
                            declarations.append(expr)
                        elif expr.startswith('(assert'):
                            assertions.append(expr)
                        current_expr = []
                else:
                    current_expr.append(line)
            
            # Process declarations
            for decl in declarations:
                if decl.startswith('(declare-sort'):
                    # Extract sort name
                    sort_name = decl.split()[1].strip()
                    self.declare_custom_sort(sort_name)
                    
                elif decl.startswith('(declare-fun'):
                    # Parse function declaration
                    parts = decl[1:-1].split()
                    if len(parts) < 4:
                        continue
                        
                    func_name = parts[1]
                    
                    # Extract argument types
                    arg_types = []
                    in_args = False
                    args_buffer = []
                    
                    for part in parts[2:]:
                        if '(' in part:
                            in_args = True
                        if in_args:
                            args_buffer.append(part)
                        if ')' in part:
                            in_args = False
                            if args_buffer:
                                arg_str = ' '.join(args_buffer)
                                arg_str = arg_str.strip('()')
                                for arg_type in arg_str.split():
                                    if arg_type in self.custom_sorts:
                                        arg_types.append(self.custom_sorts[arg_type])
                                    elif arg_type == 'Int':
                                        arg_types.append(IntSort())
                                    elif arg_type == 'Bool':
                                        arg_types.append(BoolSort())
                                    else:
                                        # Create a new sort for unknown types
                                        arg_types.append(self.declare_custom_sort(arg_type))
                                args_buffer = []
                    
                    # Get return type
                    return_type = BoolSort() if parts[-1] == 'Bool' else IntSort()
                    
                    # Create function
                    self.declarations[func_name] = Function(func_name, *arg_types, return_type)
            
            # Process assertions
            for assertion in assertions:
                try:
                    parsed = parse_smt2_string(assertion, decls=self.declarations)[0]
                    self.solver.add(parsed)
                except Exception as e:
                    logging.error(f"Error parsing assertion: {assertion}\nError: {str(e)}")
                    return False, f"Error parsing assertion: {str(e)}"
            
            return True, "Successfully parsed SMT-LIB"
            
        except Exception as e:
            logging.error(f"Error parsing SMT-LIB: {str(e)}")
            return False, f"Error parsing SMT-LIB: {str(e)}"
    
    def verify(self) -> Tuple[bool, str]:
        """Verify if the SMT-LIB expression is satisfiable."""
        try:
            result = self.solver.check()
            if result == sat:
                return True, "Expression is satisfiable"
            elif result == unsat:
                return False, "Expression is unsatisfiable"
            else:
                return False, "Solver could not determine satisfiability"
        except Exception as e:
            logging.error(f"Error during verification: {str(e)}")
            return False, f"Error during verification: {str(e)}"
    
    def get_model(self) -> Dict[str, Any]:
        """Get the model if the expression is satisfiable."""
        try:
            if self.solver.check() == sat:
                model = self.solver.model()
                return {str(d): str(model[d]) for d in model.decls()}
        except Exception as e:
            logging.error(f"Error getting model: {str(e)}")
        return {}

def test_statement(statement: str, generator: SMTLIBGenerator) -> Dict[str, Any]:
    """Test a single statement using Z3."""
    try:
        logging.info(f"Testing statement: {statement}")
        
        # Generate SMT-LIB conversion
        result = generator.generate_smtlib(statement)
        logging.info("Generated SMT-LIB conversion")
        
        if 'error' in result:
            logging.error(f"Error in SMT-LIB generation: {result['error']}")
            return {
                "statement": statement,
                "timestamp": datetime.now().isoformat(),
                "success": False,
                "error": result['error']
            }
        
        # Create verifier and parse SMT-LIB
        verifier = Z3Verifier()
        logging.info("Created Z3 verifier")
        
        logging.info(f"Parsing SMT-LIB:\n{result['smtlib_conversion']}")
        parse_success, parse_message = verifier.parse_smtlib(result['smtlib_conversion'])
        logging.info(f"Parse result: {parse_success}, {parse_message}")
        
        if not parse_success:
            logging.error(f"Failed to parse SMT-LIB: {parse_message}")
            return {
                "statement": statement,
                "timestamp": datetime.now().isoformat(),
                "success": False,
                "error": parse_message
            }
        
        # Verify satisfiability
        logging.info("Checking satisfiability")
        is_satisfiable, verify_message = verifier.verify()
        logging.info(f"Satisfiability result: {is_satisfiable}, {verify_message}")
        
        # Get model if satisfiable
        model = verifier.get_model() if is_satisfiable else {}
        if model:
            logging.info(f"Found model: {model}")
        
        # Print results
        print("\n" + "="*80)
        print(f"RFC Statement: {statement}")
        print("="*80)
        print("\nSMT-LIB Conversion:")
        print(result['smtlib_conversion'])
        print("\nVerification Result:")
        print(f"Satisfiable: {is_satisfiable}")
        print(f"Message: {verify_message}")
        if model:
            print("\nModel:")
            for var, value in model.items():
                print(f"{var} = {value}")
        print("="*80 + "\n")
        
        return {
            "statement": statement,
            "timestamp": datetime.now().isoformat(),
            "success": True,
            "smtlib_conversion": result['smtlib_conversion'],
            "is_satisfiable": is_satisfiable,
            "verification_message": verify_message,
            "model": model
        }
        
    except Exception as e:
        logging.error(f"Error testing statement: {str(e)}")
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
    
    # RFC statements to test
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
            result = test_statement(statement, generator)
            results.append(result)
        
        # Save results
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        output_file = os.path.join(output_dir, f"z3_verification_results_{timestamp}.json")
        
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