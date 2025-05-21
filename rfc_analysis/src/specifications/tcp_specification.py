from typing import Dict, List, Set

class TCPSpecification:
    def __init__(self):
        self.node_types = {'TCPEndpoint', 'Initiator', 'Responder'}
        self.states = {
            'CLOSED', 'LISTEN', 'SYN_SENT', 'SYN_RECEIVED',
            'ESTABLISHED', 'FIN_WAIT_1', 'FIN_WAIT_2',
            'CLOSE_WAIT', 'CLOSING', 'LAST_ACK', 'TIME_WAIT'
        }
        self._setup_predicates()
        self._setup_state_transitions()

    def _setup_predicates(self):
        self.node_predicates = {
            'isTCPEndpoint', 'isInitiator', 'isResponder'
        }
        
        self.message_predicates = {
            'isSYN', 'isACK', 'isRST', 'isFIN',
            'hasSequenceNumber', 'hasAckNumber'
        }
        
        self.action_predicates = {
            'sends', 'receives', 'ignores', 'responds'
        }
        
        self.state_predicates = {
            'inState', 'transitionsTo'
        }
        
        self.relation_predicates = {
            'acknowledges', 'precedes', 'follows'
        }

    def _setup_state_transitions(self):
        self.state_transitions = {
            'CLOSED': {'LISTEN', 'SYN_SENT'},
            'LISTEN': {'SYN_RECEIVED', 'CLOSED'},
            'SYN_SENT': {'ESTABLISHED', 'CLOSED'},
            'SYN_RECEIVED': {'ESTABLISHED', 'FIN_WAIT_1'},
            'ESTABLISHED': {'FIN_WAIT_1', 'CLOSE_WAIT'},
            'FIN_WAIT_1': {'FIN_WAIT_2', 'CLOSING'},
            'FIN_WAIT_2': {'TIME_WAIT'},
            'CLOSE_WAIT': {'LAST_ACK'},
            'CLOSING': {'TIME_WAIT'},
            'LAST_ACK': {'CLOSED'},
            'TIME_WAIT': {'CLOSED'}
        }

    def get_predicate_categories(self) -> Dict[str, Set[str]]:
        return {
            'node_predicates': self.node_predicates,
            'message_predicates': self.message_predicates,
            'action_predicates': self.action_predicates,
            'state_predicates': self.state_predicates,
            'relation_predicates': self.relation_predicates
        }

    def get_all_predicates(self) -> Dict[str, Set[str]]:
        return self.get_predicate_categories()

    def validate_predicate(self, predicate: str, category: str) -> bool:
        categories = self.get_predicate_categories()
        return category in categories and predicate in categories[category]

    def get_state_transitions(self, state: str) -> Set[str]:
        return self.state_transitions.get(state, set()) 