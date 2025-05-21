from .base_specification import RFCSpecification

class TCPSpecification(RFCSpecification):
    """TCP (RFC 793) Specification"""
    def __init__(self):
        super().__init__()
        self.setup_nodes()
        self.setup_messages()
        self.setup_states()
        self.setup_predicates()
        self.setup_timers()
        self.setup_connections()
    
    def setup_nodes(self):
        """Define TCP node types and their predicates"""
        self.predicates['node'] = {
            'TCPEndpoint': {
                'predicate': 'TCPEndpoint(e)',
                'description': 'e is a TCP endpoint',
                'examples': ['client', 'server']
            },
            'Initiator': {
                'predicate': 'Initiator(i)',
                'description': 'i initiates the connection',
                'examples': ['active opener']
            },
            'Responder': {
                'predicate': 'Responder(r)',
                'description': 'r responds to connection requests',
                'examples': ['passive opener']
            }
        }
    
    def setup_messages(self):
        """Define TCP message types and their predicates"""
        self.predicates['message'] = {
            'Segment': {
                'predicate': 'Segment(s)',
                'description': 's is a TCP segment',
                'components': ['header', 'data']
            },
            'HasFlag': {
                'predicate': 'HasFlag(s,flag)',
                'description': 'segment s has flag set',
                'flags': ['SYN', 'ACK', 'RST', 'FIN']
            },
            'HasSeqNum': {
                'predicate': 'HasSeqNum(s,n)',
                'description': 'segment s has sequence number n'
            },
            'HasAckNum': {
                'predicate': 'HasAckNum(s,n)',
                'description': 'segment s has acknowledgment number n'
            },
            'HasWindow': {
                'predicate': 'HasWindow(s,w)',
                'description': 'segment s has window size w'
            }
        }
    
    def setup_states(self):
        """Define TCP states and their transitions"""
        self.predicates['state'] = {
            'InState': {
                'predicate': 'InState(e,state)',
                'description': 'endpoint e is in state',
                'states': ['CLOSED', 'LISTEN', 'SYN_SENT', 'SYN_RECEIVED', 'ESTABLISHED']
            }
        }
        
        self.states = {
            'CLOSED': {
                'description': 'No connection exists',
                'transitions': ['LISTEN', 'SYN_SENT']
            },
            'LISTEN': {
                'description': 'Waiting for connection request',
                'transitions': ['SYN_RECEIVED', 'CLOSED']
            },
            'SYN_SENT': {
                'description': 'Connection request sent',
                'transitions': ['ESTABLISHED', 'CLOSED']
            },
            'SYN_RECEIVED': {
                'description': 'Connection request received',
                'transitions': ['ESTABLISHED', 'CLOSED']
            },
            'ESTABLISHED': {
                'description': 'Connection established',
                'transitions': ['FIN_WAIT_1', 'CLOSE_WAIT']
            }
        }
    
    def setup_predicates(self):
        """Define TCP-specific predicates"""
        self.predicates['action'] = {
            'Send': {
                'predicate': 'Send(e,s)',
                'description': 'endpoint e sends segment s'
            },
            'Receive': {
                'predicate': 'Receive(e,s)',
                'description': 'endpoint e receives segment s'
            },
            'Process': {
                'predicate': 'Process(e,s)',
                'description': 'endpoint e processes segment s'
            },
            'Drop': {
                'predicate': 'Drop(e,s)',
                'description': 'endpoint e drops segment s'
            }
        }
        
        self.predicates['relation'] = {
            'AcknowledgesSegment': {
                'predicate': 'AcknowledgesSegment(s1,s2)',
                'description': 'segment s1 acknowledges s2'
            },
            'RetransmissionOf': {
                'predicate': 'RetransmissionOf(s1,s2)',
                'description': 'segment s1 is retransmission of s2'
            }
        }
    
    def setup_timers(self):
        """Define timer-related predicates"""
        self.predicates['timer'] = {
            'HasTimer': {
                'predicate': 'HasTimer(e,s,t)',
                'description': 'endpoint e has timer t for segment s'
            },
            'TimerExpires': {
                'predicate': 'TimerExpires(e,s)',
                'description': 'timer for segment s at endpoint e expires'
            }
        }
    
    def setup_connections(self):
        """Define connection-related predicates"""
        self.predicates['connection'] = {
            'Connection': {
                'predicate': 'Connection(e,c)',
                'description': 'endpoint e has connection c'
            },
            'HasWindow': {
                'predicate': 'HasWindow(e,c,w)',
                'description': 'connection c at endpoint e has window size w'
            }
        } 