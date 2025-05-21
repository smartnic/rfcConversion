from typing import List, Dict, Any
import re

class SMTLIBGenerator:
    """Generates SMT-LIB expressions for TCP RFC statements."""
    
    def __init__(self):
        self.predicates = {
            'sequence_number': 'has_sequence_number',
            'flag': 'has_flag',
            'state': 'in_state',
            'window_size': 'has_window_size',
            'source_port': 'has_source_port',
            'destination_port': 'has_destination_port',
            'socket': 'has_socket',
            'tcp_endpoint': 'is_tcp_endpoint'
        }
        
        self.sorts = {
            'Message': 'Message',
            'Node': 'Node',
            'State': 'State',
            'Port': 'Port',
            'Number': 'Int',
            'WindowSize': 'Int',
            'Socket': 'Socket'
        }
    
    def generate_smtlib(self, statement: str) -> Dict[str, Any]:
        """Generate SMT-LIB expression for a given statement."""
        try:
            # Extract key components from statement
            components = self._analyze_statement(statement)
            
            # Generate declarations
            declarations = self._generate_declarations(components)
            
            # Generate assertions
            assertions = self._generate_assertions(statement, components)
            
            # Combine into full SMT-LIB expression
            smtlib = declarations + '\n\n' + assertions
            
            # Extract used predicates
            used_predicates = self._extract_used_predicates(components)
            
            # Generate explanation
            explanation = self._generate_explanation(statement, components)
            
            return {
                'smtlib_conversion': smtlib,
                'predicates_used': used_predicates,
                'explanation': explanation
            }
            
        except Exception as e:
            return {
                'error': str(e),
                'smtlib_conversion': '',
                'predicates_used': [],
                'explanation': ''
            }
    
    def _analyze_statement(self, statement: str) -> Dict[str, Any]:
        """Analyze statement to extract key components."""
        components = {
            'subjects': [],
            'predicates': [],
            'objects': [],
            'quantifiers': []
        }
        
        # Simple pattern matching for common TCP statements
        if 'sequence number' in statement:
            components['predicates'].append('sequence_number')
            components['subjects'].append('Message')
            components['objects'].append('Number')
            
        elif 'flag' in statement:
            components['predicates'].append('flag')
            components['subjects'].append('Message')
            components['objects'].append('String')
            
        elif 'state' in statement:
            components['predicates'].append('state')
            components['subjects'].append('Node')
            components['objects'].append('State')
            
        elif 'window size' in statement:
            components['predicates'].append('window_size')
            components['subjects'].append('Node')
            components['objects'].append('WindowSize')
            
        elif 'port' in statement:
            if 'source' in statement:
                components['predicates'].append('source_port')
            else:
                components['predicates'].append('destination_port')
            components['subjects'].append('Message')
            components['objects'].append('Port')
            
        elif 'socket' in statement:
            components['predicates'].append('socket')
            components['subjects'].append('Node')
            components['objects'].append('Socket')
            
        return components
    
    def _generate_declarations(self, components: Dict[str, Any]) -> str:
        """Generate SMT-LIB declarations."""
        declarations = []
        
        # Add sort declarations
        for subject in components['subjects']:
            if subject in self.sorts:
                declarations.append(f'(declare-sort {self.sorts[subject]})')
        
        # Add predicate declarations
        for predicate in components['predicates']:
            if predicate in self.predicates:
                pred_name = self.predicates[predicate]
                # Get the object type for this predicate
                obj_type = next((obj for obj in components['objects'] if obj in self.sorts), 'Int')
                declarations.append(f'(declare-fun {pred_name} ({self.sorts[components["subjects"][0]]} {self.sorts[obj_type]}) Bool)')
        
        return '\n'.join(declarations)
    
    def _generate_assertions(self, statement: str, components: Dict[str, Any]) -> str:
        """Generate SMT-LIB assertions."""
        if not components['predicates']:
            return ''
            
        predicate = self.predicates[components['predicates'][0]]
        subject = components['subjects'][0]
        obj_type = next((obj for obj in components['objects'] if obj in self.sorts), 'Int')
        
        # Generate appropriate assertion based on statement type
        if 'must have' in statement or 'has' in statement:
            return f'(assert (forall ((x {self.sorts[subject]}))\n  (exists ((y {self.sorts[obj_type]}))\n    ({predicate} x y))))'
        elif 'must be' in statement:
            return f'(assert (forall ((x {self.sorts[subject]}))\n  ({predicate} x)))'
        else:
            return f'(assert (exists ((x {self.sorts[subject]}))\n  ({predicate} x)))'
    
    def _extract_used_predicates(self, components: Dict[str, Any]) -> List[str]:
        """Extract list of predicates used in the conversion."""
        return [self.predicates[p] for p in components['predicates'] if p in self.predicates]
    
    def _generate_explanation(self, statement: str, components: Dict[str, Any]) -> str:
        """Generate explanation for the SMT-LIB conversion."""
        if not components['predicates']:
            return 'Could not generate SMT-LIB conversion for this statement.'
            
        predicate = self.predicates[components['predicates'][0]]
        subject = components['subjects'][0]
        obj_type = next((obj for obj in components['objects'] if obj in self.sorts), 'Int')
        
        return f"""We declare the necessary sorts and functions for this TCP requirement. The SMT-LIB expression:
1. Declares the {subject} sort to represent TCP entities
2. Declares the {obj_type} sort for the property values
3. Defines the {predicate} predicate to relate {subject}s to their {obj_type} values
4. Uses quantifiers to express that every {subject} must have a corresponding {obj_type} value""" 