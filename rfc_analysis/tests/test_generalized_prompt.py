from ..prompts.generalized_rfc_prompt import get_generalized_rfc_prompt

def test_generalized_prompt():
    """Test the generalized prompt with various RFC requirements"""
    prompt = get_generalized_rfc_prompt()
    
    # Example RFC requirements to test
    requirements = [
        {
            'requirement': 'A node must maintain a sequence number for each message sent.',
            'expected_predicates': ['Node', 'Send', 'Message', 'HasField', 'SequenceNumber']
        },
        {
            'requirement': 'When a node receives a message with an invalid checksum, it must drop the message.',
            'expected_predicates': ['Node', 'Receive', 'Message', 'HasField', 'Checksum', 'Drop']
        },
        {
            'requirement': 'A node in the ESTABLISHED state must respond to keep-alive messages.',
            'expected_predicates': ['Node', 'InState', 'Message', 'HasType', 'Send']
        },
        {
            'requirement': 'Each connection must maintain a maximum segment size.',
            'expected_predicates': ['Node', 'Connection', 'HasProperty', 'MaxSegmentSize']
        },
        {
            'requirement': 'A node must retransmit a message if no acknowledgment is received within the timeout period.',
            'expected_predicates': ['Node', 'Send', 'Message', 'TimerExpires', 'RelatedTo']
        }
    ]
    
    # Test each requirement
    for req in requirements:
        print(f"\nTesting requirement: {req['requirement']}")
        
        # Replace the placeholder in the prompt with the current requirement
        current_prompt = prompt.replace("[RFC Requirement]", req['requirement'])
        
        # Print the relevant part of the prompt
        print("\nPrompt section:")
        print(current_prompt.split("# Task")[0])
        
        # Print expected predicates
        print("\nExpected predicates:")
        for pred in req['expected_predicates']:
            print(f"- {pred}")
        
        # Print example FOL representation
        print("\nExample FOL representation:")
        if "sequence number" in req['requirement']:
            print("∀n ∀m (Node(n) ∧ Send(n,m) → ∃s (HasField(m,s) ∧ SequenceNumber(s)))")
        elif "invalid checksum" in req['requirement']:
            print("∀n ∀m (Node(n) ∧ Receive(n,m) ∧ HasField(m,c) ∧ ¬ValidChecksum(c) → Drop(n,m))")
        elif "ESTABLISHED state" in req['requirement']:
            print("∀n ∀m (Node(n) ∧ InState(n,ESTABLISHED) ∧ Receive(n,m) ∧ HasType(m,KEEP_ALIVE) → ∃r (Send(n,r) ∧ ResponseTo(r,m)))")
        elif "maximum segment size" in req['requirement']:
            print("∀n ∀c (Node(n) ∧ Connection(n,c) → ∃s HasProperty(n,c,s) ∧ MaxSegmentSize(s))")
        elif "retransmit" in req['requirement']:
            print("∀n ∀m (Node(n) ∧ Send(n,m) ∧ TimerExpires(n,m) → ∃m' (RelatedTo(m',m) ∧ Send(n,m')))")

if __name__ == '__main__':
    test_generalized_prompt() 