from z3 import *
from typing import Dict, Any, List, Tuple
import logging

class Z3Generator:
    def __init__(self):
        self.sorts = {}
        self.functions = {}
        self.constants = {}
        
    def declare_sort(self, name: str) -> SortRef:
        """Declare a new sort if it doesn't exist."""
        if name not in self.sorts:
            self.sorts[name] = DeclareSort(name)
        return self.sorts[name]
    
    def declare_function(self, name: str, arg_types: List[SortRef], return_type: SortRef) -> FuncDeclRef:
        """Declare a new function if it doesn't exist."""
        if name not in self.functions:
            self.functions[name] = Function(name, *arg_types, return_type)
        return self.functions[name]
    
    def declare_constant(self, name: str, sort: SortRef) -> ExprRef:
        """Declare a new constant if it doesn't exist."""
        if name not in self.constants:
            self.constants[name] = Const(name, sort)
        return self.constants[name]
    
    def generate_z3_code(self, statement: str) -> Dict[str, Any]:
        """Generate Z3 Python API code for a TCP requirement."""
        try:
            # Initialize solver
            solver = Solver()
            
            # Declare basic sorts
            Message = self.declare_sort('Message')
            Node = self.declare_sort('Node')
            Port = self.declare_sort('Port')
            State = self.declare_sort('State')
            Socket = self.declare_sort('Socket')
            Flag = self.declare_sort('Flag')
            
            # Declare common functions
            has_sequence_number = self.declare_function('has_sequence_number', [Message, IntSort()], BoolSort())
            has_source_port = self.declare_function('has_source_port', [Message, Port], BoolSort())
            has_destination_port = self.declare_function('has_destination_port', [Message, Port], BoolSort())
            has_flag = self.declare_function('has_flag', [Message, Flag], BoolSort())
            in_state = self.declare_function('in_state', [Node, State], BoolSort())
            has_window_size = self.declare_function('has_window_size', [Node, IntSort()], BoolSort())
            has_socket = self.declare_function('has_socket', [Node, Socket], BoolSort())
            
            # Generate requirement based on statement
            if "sequence number" in statement.lower():
                # Create variables
                m = Const('m', Message)
                n = Const('n', IntSort())
                
                # Create requirement
                requirement = ForAll([m], Exists([n], has_sequence_number(m, n)))
                
            elif "source port" in statement.lower():
                m = Const('m', Message)
                p = Const('p', Port)
                requirement = ForAll([m], Exists([p], has_source_port(m, p)))
                
            elif "destination port" in statement.lower():
                m = Const('m', Message)
                p = Const('p', Port)
                requirement = ForAll([m], Exists([p], has_destination_port(m, p)))
                
            elif "state" in statement.lower():
                n = Const('n', Node)
                s = Const('s', State)
                requirement = ForAll([n], Exists([s], in_state(n, s)))
                
            elif "window size" in statement.lower():
                n = Const('n', Node)
                w = Const('w', IntSort())
                requirement = ForAll([n], Exists([w], has_window_size(n, w)))
                
            elif "socket" in statement.lower():
                n = Const('n', Node)
                s = Const('s', Socket)
                requirement = ForAll([n], Exists([s], has_socket(n, s)))
                
            else:
                return {
                    "success": False,
                    "error": f"Unsupported statement: {statement}"
                }
            
            # Add requirement to solver
            solver.add(requirement)
            
            # Generate Python code
            code = f"""from z3 import *

# Create solver
solver = Solver()

# Declare sorts
{chr(10).join(f"{sort} = DeclareSort('{sort}')" for sort in self.sorts.keys())}

# Declare functions
{chr(10).join(f"{func} = Function('{func}', {', '.join(str(t) for t in self.functions[func].domain())}, {self.functions[func].range()})" for func in self.functions.keys())}

# Create variables
{chr(10).join(f"{var} = Const('{var}', {var.type()})" for var in requirement.vars())}

# Create requirement
requirement = {requirement}

# Add to solver
solver.add(requirement)

# Check satisfiability
result = solver.check()
if result == sat:
    print("The formula is satisfiable!")
    model = solver.model()
    print("\\nModel:")
    for d in model.decls():
        print(f"{{d.name()}} = {{model[d]}}")
else:
    print("The formula is unsatisfiable!")
"""
            
            return {
                "success": True,
                "z3_code": code,
                "requirement": str(requirement),
                "solver": solver
            }
            
        except Exception as e:
            logging.error(f"Error generating Z3 code: {str(e)}")
            return {
                "success": False,
                "error": str(e)
            }

def main():
    # Test the generator
    generator = Z3Generator()
    statements = [
        "A TCP segment has a sequence number.",
        "A TCP segment has a source port.",
        "A TCP endpoint has a state.",
        "A TCP endpoint has a window size.",
        "A TCP endpoint has a socket."
    ]
    
    for statement in statements:
        print(f"\nTesting statement: {statement}")
        result = generator.generate_z3_code(statement)
        
        if result["success"]:
            print("\nGenerated Z3 code:")
            print(result["z3_code"])
            
            # Test the generated code
            print("\nTesting satisfiability...")
            solver = result["solver"]
            if solver.check() == sat:
                print("The formula is satisfiable!")
                model = solver.model()
                print("\nModel:")
                for d in model.decls():
                    print(f"{d.name()} = {model[d]}")
            else:
                print("The formula is unsatisfiable!")
        else:
            print(f"Error: {result['error']}")

if __name__ == "__main__":
    main() 