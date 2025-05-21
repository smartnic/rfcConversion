from rfc_analysis.src.generators.z3_generator import Z3Generator
import logging

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

def test_complex_requirement():
    generator = Z3Generator()
    
    # Complex TCP requirement
    statement = """
    On the ESTABLISHED state, the initial segment's sequence number must equal 
    the initial sequence number for a given node and socket.
    """
    
    logger.info(f"Testing complex requirement: {statement}")
    result = generator.generate_z3_code(statement)
    
    if result["success"]:
        logger.info("\nGenerated Z3 code:")
        logger.info(result["z3_code"])
        
        # Test the generated code
        logger.info("\nTesting satisfiability...")
        solver = result["solver"]
        if solver.check() == sat:
            logger.info("The formula is satisfiable!")
            model = solver.model()
            logger.info("\nModel:")
            for d in model.decls():
                logger.info(f"{d.name()} = {model[d]}")
        else:
            logger.info("The formula is unsatisfiable!")
    else:
        logger.error(f"Error: {result['error']}")

if __name__ == "__main__":
    test_complex_requirement() 