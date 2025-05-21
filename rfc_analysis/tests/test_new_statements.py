import os
import sys

# Add the parent directory to the Python path
current_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(current_dir)
sys.path.insert(0, parent_dir)

from src.tcp_specification import TCPSpecification
from examples.tcp_examples import TCPExample

def test_new_rfc_statements():
    """Test new RFC statements with our implementation"""
    tcp_spec = TCPSpecification()
    
    # New RFC statements to test
    new_statements = [
        {
            'requirement': 'A TCP endpoint must maintain a retransmission timer for each segment sent.',
            'expected_predicates': ['TCPEndpoint', 'Send', 'Segment', 'HasTimer']
        },
        {
            'requirement': 'When a retransmission timer expires, the endpoint must retransmit the segment.',
            'expected_predicates': ['TimerExpires', 'RetransmissionOf', 'Send']
        },
        {
            'requirement': 'A TCP endpoint must not send a RST segment in response to a RST segment.',
            'expected_predicates': ['TCPEndpoint', 'Receive', 'HasFlag', 'Send']
        },
        {
            'requirement': 'A TCP endpoint must not send a SYN segment while in the ESTABLISHED state.',
            'expected_predicates': ['TCPEndpoint', 'InState', 'Send', 'HasFlag']
        },
        {
            'requirement': 'A TCP endpoint must maintain a window size for each connection.',
            'expected_predicates': ['TCPEndpoint', 'HasWindow', 'Connection']
        }
    ]
    
    # Test each statement
    for statement in new_statements:
        print(f"\nTesting statement: {statement['requirement']}")
        
        # Get all predicates from the specification
        all_predicates = set()
        for category in tcp_spec.predicates.values():
            for predicate_name in category:
                all_predicates.add(predicate_name)
        
        # Verify that all expected predicates exist in our specification
        missing_predicates = []
        for predicate in statement['expected_predicates']:
            if predicate not in all_predicates:
                missing_predicates.append(predicate)
        
        if missing_predicates:
            print(f"Missing predicates: {missing_predicates}")
        else:
            print("All required predicates are defined in the specification")
        
        # Generate FOL representation (this would be done by the model in practice)
        print("\nExample FOL representation:")
        if "retransmission timer" in statement['requirement']:
            print("∀e ∀s (TCPEndpoint(e) ∧ Send(e,s) → ∃t HasTimer(e,s,t))")
        elif "retransmission timer expires" in statement['requirement']:
            print("∀e ∀s (TCPEndpoint(e) ∧ TimerExpires(e,s) → ∃s' (RetransmissionOf(s',s) ∧ Send(e,s')))")
        elif "RST segment" in statement['requirement']:
            print("∀e ∀s (TCPEndpoint(e) ∧ Receive(e,s) ∧ HasFlag(s,RST) → ¬∃r (Segment(r) ∧ HasFlag(r,RST) ∧ Send(e,r)))")
        elif "SYN segment" in statement['requirement']:
            print("∀e ∀s (TCPEndpoint(e) ∧ InState(e,ESTABLISHED) → ¬(Send(e,s) ∧ HasFlag(s,SYN)))")
        elif "window size" in statement['requirement']:
            print("∀e ∀c (TCPEndpoint(e) ∧ Connection(e,c) → ∃w HasWindow(e,c,w))")

if __name__ == '__main__':
    test_new_rfc_statements() 