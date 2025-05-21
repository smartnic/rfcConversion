from z3 import *
import logging

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler()
    ]
)

def test_complex_requirement():
    try:
        # Create solver
        solver = Solver()
        
        # Declare sorts
        Message = DeclareSort('Message')
        Node = DeclareSort('Node')
        Port = DeclareSort('Port')
        State = DeclareSort('State')
        Socket = DeclareSort('Socket')
        Flag = DeclareSort('Flag')
        
        # Declare functions
        has_sequence_number = Function('has_sequence_number', Message, IntSort(), BoolSort())
        has_socket = Function('has_socket', Node, Socket, BoolSort())
        in_state = Function('in_state', Node, State, BoolSort())
        initial_seq = Function('initial_seq', Node, Socket, IntSort())
        init_segment = Function('init_segment', Node, Socket, Message)
        
        # Declare constant
        ESTABLISHED = Const('ESTABLISHED', State)
        
        # Create variables for quantification
        n = Const('n', Node)
        s = Const('s', Socket)
        
        # Create the requirement
        requirement = ForAll([n, s],
            Implies(
                And(
                    has_socket(n, s),
                    in_state(n, ESTABLISHED)
                ),
                has_sequence_number(
                    init_segment(n, s),
                    initial_seq(n, s)
                )
            )
        )
        
        # Add to solver
        solver.add(requirement)
        
        # Check satisfiability
        logging.info("Checking satisfiability...")
        result = solver.check()
        
        if result == sat:
            logging.info("The formula is satisfiable!")
            # Get model
            model = solver.model()
            logging.info("\nModel:")
            for d in model.decls():
                logging.info(f"{d.name()} = {model[d]}")
        elif result == unsat:
            logging.info("The formula is unsatisfiable!")
        else:
            logging.info("Solver could not determine satisfiability")
            
    except Exception as e:
        logging.error(f"Error during verification: {str(e)}")
        raise

if __name__ == "__main__":
    test_complex_requirement() 