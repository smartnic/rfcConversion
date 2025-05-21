import sys
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.prompts.tcp_rfc_prompt import get_tcp_rfc_prompt

# RFC statements to test
RFC_STATEMENTS = [
    {
        'id': 1,
        'statement': 'The sequence number field is a 32-bit number that identifies the first data octet in this segment.'
    },
    {
        'id': 2,
        'statement': 'The urgent pointer is interpreted only if the URG control bit is set.'
    },
    {
        'id': 3,
        'statement': 'A TCP connection is established by the exchange of a SYN, a SYN-ACK, and an ACK.'
    },
    {
        'id': 4,
        'statement': 'If no acknowledgment is received before the timer expires, the segment is retransmitted.'
    },
    {
        'id': 5,
        'statement': 'The window field is a 16-bit field that specifies the size of the receive window.'
    }
]

def test_model_output():
    """Test model output for each RFC statement"""
    prompt = get_tcp_rfc_prompt()
    
    print("\nTesting Model Output for RFC Statements")
    print("=======================================")
    
    for statement in RFC_STATEMENTS:
        print(f"\nStatement {statement['id']}:")
        print(f"RFC Statement: {statement['statement']}")
        
        # Replace the placeholder in the prompt with the current statement
        current_prompt = prompt.replace("[TCP Requirement]", statement['statement'])
        
        print("\nModel Output:")
        print("------------")
        print(current_prompt)
        print("\n" + "="*80)

if __name__ == '__main__':
    test_model_output() 