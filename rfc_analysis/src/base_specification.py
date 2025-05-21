from typing import Dict, List, Any

class RFCSpecification:
    """Base class for RFC specifications"""
    def __init__(self):
        self.node_types = {}
        self.message_types = {}
        self.states = {}
        self.actions = {}
        self.predicates = {
            'node': {},
            'message': {},
            'action': {},
            'state': {},
            'relation': {},
            'timer': {},
            'connection': {}
        }
    
    def get_predicate_categories(self) -> List[str]:
        """Return all predicate categories"""
        return list(self.predicates.keys())
    
    def get_all_predicates(self) -> Dict[str, Dict[str, Any]]:
        """Return all predicates organized by category"""
        all_predicates = {}
        
        # Add node predicates
        all_predicates['node'] = {
            name: info['predicate']
            for name, info in self.node_types.items()
        }
        
        # Add message predicates
        all_predicates['message'] = {}
        for msg_type, info in self.message_types.items():
            if 'predicate' in info:
                all_predicates['message'][msg_type] = info['predicate']
            if 'components' in info:
                for component in info.get('components', []):
                    if isinstance(component, dict):
                        for comp_name, comp_info in component.items():
                            if 'predicate' in comp_info:
                                all_predicates['message'][comp_name] = comp_info['predicate']
        
        # Add flag predicates
        if 'Flags' in self.message_types:
            for flag, info in self.message_types['Flags'].items():
                all_predicates['message'][flag] = info['predicate']
        
        # Add header field predicates
        if 'HeaderFields' in self.message_types:
            for field, info in self.message_types['HeaderFields'].items():
                all_predicates['message'][field] = info['predicate']
        
        # Add action predicates
        all_predicates['action'] = {
            name: info['predicate']
            for name, info in self.actions.items()
        }
        
        # Add state predicates
        all_predicates['state'] = {
            name: info['predicate']
            for name, info in self.states.items()
        }
        
        # Add other predicate categories
        for category in ['relation', 'timer', 'connection']:
            if category in self.predicates:
                all_predicates[category] = {
                    name: info['predicate']
                    for name, info in self.predicates[category].items()
                }
        
        return all_predicates
    
    def get_state_transitions(self, from_state: str) -> List[str]:
        """Return possible transitions from a given state"""
        if from_state in self.states:
            return self.states[from_state].get('transitions', [])
        return []
    
    def validate_predicate(self, predicate: str, category: str = None) -> bool:
        """Validate if a predicate exists in the specification"""
        all_predicates = self.get_all_predicates()
        if category:
            return category in all_predicates and predicate in all_predicates[category]
        return any(predicate in cat_predicates for cat_predicates in all_predicates.values()) 