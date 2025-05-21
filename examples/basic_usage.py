"""
Basic example of using the RFC to FOL converter.
"""

from rfc_analysis.src.converter import RFCConverter
from rfc_analysis.src.generators.smtlib_generator import SMTLibGenerator
from rfc_analysis.src.generators.z3_generator import Z3Generator

def main():
    # Example TCP RFC statement
    statement = """
    If a TCP segment arrives with a sequence number that is less than the expected 
    sequence number, the segment should be discarded.
    """
    
    print("Original RFC statement:")
    print(statement.strip())
    print("\n" + "="*80 + "\n")
    
    # Convert to SMT-LIB
    converter = RFCConverter()
    smtlib_expr = converter.convert_to_smtlib(statement)
    
    print("SMT-LIB Expression:")
    print(smtlib_expr)
    print("\n" + "="*80 + "\n")
    
    # Generate SMT-LIB code
    generator = SMTLibGenerator()
    smtlib_code = generator.generate(smtlib_expr)
    
    print("Generated SMT-LIB Code:")
    print(smtlib_code)
    print("\n" + "="*80 + "\n")
    
    # Verify using Z3
    z3_generator = Z3Generator()
    result = z3_generator.verify_statement(statement)
    
    print("Z3 Verification Result:")
    print(f"Statement is {result}")

if __name__ == "__main__":
    main() 