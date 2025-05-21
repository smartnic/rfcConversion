from typing import List, Dict, Tuple

class TCPExample:
    """Example TCP requirements and their FOL representations"""
    
    @staticmethod
    def get_examples() -> List[Dict[str, str]]:
        """Return a list of TCP requirements and their FOL representations"""
        return [
            {
                'requirement': 'A SYN segment must have a sequence number.',
                'fol': '∀s (Segment(s) ∧ HasFlag(s,SYN) → ∃n HasSeqNum(s,n))',
                'explanation': 'For all segments s, if s is a segment and has the SYN flag set, then there exists a sequence number n such that s has sequence number n.'
            },
            {
                'requirement': 'When in CLOSED state, a TCP endpoint must respond to any incoming segment with a RST.',
                'fol': '∀e ∀s (TCPEndpoint(e) ∧ InState(e,CLOSED) ∧ Receive(e,s) → ∃r (Segment(r) ∧ HasFlag(r,RST) ∧ Send(e,r)))',
                'explanation': 'For all endpoints e and segments s, if e is a TCP endpoint in CLOSED state and receives s, then there exists a segment r with RST flag set that e sends.'
            },
            {
                'requirement': 'A TCP endpoint in LISTEN state must ignore RST segments.',
                'fol': '∀e ∀s (TCPEndpoint(e) ∧ InState(e,LISTEN) ∧ Receive(e,s) ∧ HasFlag(s,RST) → Drop(e,s))',
                'explanation': 'For all endpoints e and segments s, if e is a TCP endpoint in LISTEN state and receives a segment s with RST flag set, then e drops s.'
            },
            {
                'requirement': 'Upon receiving a valid SYN segment in LISTEN state, a TCP endpoint must transition to SYN_RECEIVED state.',
                'fol': '∀e ∀s (TCPEndpoint(e) ∧ InState(e,LISTEN) ∧ Receive(e,s) ∧ HasFlag(s,SYN) ∧ ∃n HasSeqNum(s,n) → InState(e,SYN_RECEIVED))',
                'explanation': 'For all endpoints e and segments s, if e is a TCP endpoint in LISTEN state and receives a segment s with SYN flag set and a sequence number, then e transitions to SYN_RECEIVED state.'
            },
            {
                'requirement': 'An ACK segment must acknowledge a previously received sequence number.',
                'fol': '∀s1 ∀s2 (Segment(s1) ∧ HasFlag(s1,ACK) ∧ HasAckNum(s1,n) → ∃s2 (Segment(s2) ∧ HasSeqNum(s2,n) ∧ AcknowledgesSegment(s1,s2)))',
                'explanation': 'For all segments s1 and s2, if s1 is a segment with ACK flag set and acknowledgment number n, then there exists a segment s2 with sequence number n that s1 acknowledges.'
            }
        ]
    
    @staticmethod
    def get_state_transitions() -> List[Tuple[str, str, str]]:
        """Return a list of valid TCP state transitions"""
        return [
            ('CLOSED', 'LISTEN', 'Passive open'),
            ('CLOSED', 'SYN_SENT', 'Active open'),
            ('LISTEN', 'SYN_RECEIVED', 'Receive SYN'),
            ('SYN_SENT', 'ESTABLISHED', 'Receive SYN+ACK'),
            ('SYN_RECEIVED', 'ESTABLISHED', 'Receive ACK'),
            ('ESTABLISHED', 'FIN_WAIT_1', 'Send FIN'),
            ('ESTABLISHED', 'CLOSE_WAIT', 'Receive FIN')
        ]
    
    @staticmethod
    def get_message_sequences() -> List[Dict[str, str]]:
        """Return example TCP message sequences"""
        return [
            {
                'name': 'Three-way handshake',
                'sequence': [
                    'Initiator sends SYN',
                    'Responder sends SYN+ACK',
                    'Initiator sends ACK'
                ],
                'fol': '∃i ∃r ∃s1 ∃s2 ∃s3 (Initiator(i) ∧ Responder(r) ∧ Send(i,s1) ∧ HasFlag(s1,SYN) ∧ Send(r,s2) ∧ HasFlag(s2,SYN) ∧ HasFlag(s2,ACK) ∧ Send(i,s3) ∧ HasFlag(s3,ACK))'
            },
            {
                'name': 'Connection termination',
                'sequence': [
                    'Endpoint sends FIN',
                    'Other endpoint sends ACK',
                    'Other endpoint sends FIN',
                    'First endpoint sends ACK'
                ],
                'fol': '∃e1 ∃e2 ∃s1 ∃s2 ∃s3 ∃s4 (TCPEndpoint(e1) ∧ TCPEndpoint(e2) ∧ Send(e1,s1) ∧ HasFlag(s1,FIN) ∧ Send(e2,s2) ∧ HasFlag(s2,ACK) ∧ Send(e2,s3) ∧ HasFlag(s3,FIN) ∧ Send(e1,s4) ∧ HasFlag(s4,ACK))'
            }
        ] 