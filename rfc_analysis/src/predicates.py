from enum import Enum
from typing import Dict, List

class PredicateCategory(Enum):
    """Categories of predicates used in RFC specifications"""
    NODE = "node"
    MESSAGE = "message"
    ACTION = "action"
    STATE = "state"
    RELATION = "relation"

class PredicateType:
    """Base class for predicate types"""
    def __init__(self, name: str, predicate: str, description: str):
        self.name = name
        self.predicate = predicate
        self.description = description

class NodePredicate(PredicateType):
    """Predicates related to nodes in the protocol"""
    def __init__(self, name: str, predicate: str, description: str, examples: List[str] = None):
        super().__init__(name, predicate, description)
        self.examples = examples or []

class MessagePredicate(PredicateType):
    """Predicates related to messages in the protocol"""
    def __init__(self, name: str, predicate: str, description: str, components: List[str] = None):
        super().__init__(name, predicate, description)
        self.components = components or []

class ActionPredicate(PredicateType):
    """Predicates related to actions performed by nodes"""
    def __init__(self, name: str, predicate: str, description: str):
        super().__init__(name, predicate, description)

class StatePredicate(PredicateType):
    """Predicates related to protocol states"""
    def __init__(self, name: str, predicate: str, description: str, transitions: List[str] = None):
        super().__init__(name, predicate, description)
        self.transitions = transitions or []

class RelationPredicate(PredicateType):
    """Predicates describing relationships between protocol elements"""
    def __init__(self, name: str, predicate: str, description: str):
        super().__init__(name, predicate, description)

# Example predicate definitions
TCP_PREDICATES: Dict[PredicateCategory, Dict[str, PredicateType]] = {
    PredicateCategory.NODE: {
        'TCPEndpoint': NodePredicate(
            'TCPEndpoint',
            'TCPEndpoint(e)',
            'e is a TCP endpoint',
            ['client', 'server']
        ),
        'Initiator': NodePredicate(
            'Initiator',
            'Initiator(i)',
            'i initiates the connection',
            ['active opener']
        ),
        'Responder': NodePredicate(
            'Responder',
            'Responder(r)',
            'r responds to connection requests',
            ['passive opener']
        )
    },
    PredicateCategory.MESSAGE: {
        'Segment': MessagePredicate(
            'Segment',
            'Segment(s)',
            's is a TCP segment',
            ['header', 'data']
        ),
        'HasFlag': MessagePredicate(
            'HasFlag',
            'HasFlag(s,flag)',
            'segment s has flag set',
            ['SYN', 'ACK', 'RST', 'FIN']
        ),
        'HasSeqNum': MessagePredicate(
            'HasSeqNum',
            'HasSeqNum(s,n)',
            'segment s has sequence number n',
            ['sequence number']
        )
    },
    PredicateCategory.ACTION: {
        'Send': ActionPredicate(
            'Send',
            'Send(e,s)',
            'endpoint e sends segment s'
        ),
        'Receive': ActionPredicate(
            'Receive',
            'Receive(e,s)',
            'endpoint e receives segment s'
        ),
        'Process': ActionPredicate(
            'Process',
            'Process(e,s)',
            'endpoint e processes segment s'
        )
    },
    PredicateCategory.STATE: {
        'InState': StatePredicate(
            'InState',
            'InState(e,state)',
            'endpoint e is in state',
            ['CLOSED', 'LISTEN', 'SYN_SENT', 'SYN_RECEIVED', 'ESTABLISHED']
        )
    },
    PredicateCategory.RELATION: {
        'AcknowledgesSegment': RelationPredicate(
            'AcknowledgesSegment',
            'AcknowledgesSegment(s1,s2)',
            'segment s1 acknowledges s2'
        ),
        'RetransmissionOf': RelationPredicate(
            'RetransmissionOf',
            'RetransmissionOf(s1,s2)',
            'segment s1 is retransmission of s2'
        )
    }
} 