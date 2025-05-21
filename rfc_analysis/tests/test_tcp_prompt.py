import sys
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.prompts.tcp_rfc_prompt import get_tcp_rfc_prompt

def test_tcp_prompt():
    """Test the TCP-specific prompt with various RFC 793 requirements"""
    prompt = get_tcp_rfc_prompt()
    
    # Example TCP requirements to test
    requirements = [
        {
            'requirement': 'A TCP endpoint in LISTEN state must ignore RST segments.',
            'expected_predicates': ['TCPState', 'Receive', 'RST', 'ignores']
        },
        {
            'requirement': 'Upon receiving a valid SYN segment in LISTEN state, a TCP endpoint must transition to SYN_RECEIVED state.',
            'expected_predicates': ['TCPState', 'Receive', 'SYN', 'transitionsTo']
        },
        {
            'requirement': 'A TCP endpoint must maintain a retransmission timer for each segment sent.',
            'expected_predicates': ['TCPImplementation', 'Send', 'TimerExpired']
        },
        {
            'requirement': 'The sequence number in a SYN segment must be within the valid range.',
            'expected_predicates': ['SYN', 'SequenceNumber', 'BitLength']
        },
        {
            'requirement': 'A TCP endpoint must acknowledge all received data segments.',
            'expected_predicates': ['Receive', 'ACK', 'Send', 'Acknowledges']
        }
    ]
    
    # Test each requirement
    for req in requirements:
        print(f"\nTesting requirement: {req['requirement']}")
        
        # Print expected predicates
        print("Expected predicates:")
        for pred in req['expected_predicates']:
            print(f"- {pred}")
        
        # Print example FOL representation
        print("\nExample FOL representation:")
        if "LISTEN state" in req['requirement'] and "RST" in req['requirement']:
            print("∀t ∀m (TCPState(t,LISTEN) ∧ Receive(t,m) ∧ RST(m) → ignores(t,m))")
        elif "SYN segment" in req['requirement'] and "LISTEN" in req['requirement']:
            print("∀t ∀m (TCPState(t,LISTEN) ∧ Receive(t,m) ∧ SYN(m) → transitionsTo(t,SYN_RECEIVED))")
        elif "retransmission timer" in req['requirement']:
            print("∀t ∀m (Send(t,m) → ∃timer TimerExpired(timer,m))")
        elif "sequence number" in req['requirement'] and "SYN" in req['requirement']:
            print("∀m ∀n (SYN(m) ∧ SequenceNumber(m,n) → BitLength(n,32))")
        elif "acknowledge" in req['requirement']:
            print("∀t ∀m (Receive(t,m) → ∃a (Send(t,a) ∧ ACK(a) ∧ Acknowledges(a,m)))")

if __name__ == '__main__':
    test_tcp_prompt() 