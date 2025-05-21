def get_tcp_rfc_prompt():
    """Returns the base prompt template for TCP RFC statement conversion."""
    return """
# Introduction
You are tasked with converting TCP protocol requirements from RFC 793 into both First-Order Logic (FOL) and SMT-LIB format. The requirement to convert is:

"[TCP Requirement]"

# Protocol Elements
The TCP protocol involves the following key elements:
- Nodes: TCPEndpoint (base type), Initiator, Responder
- Messages: TCPSegment with fields (sequence_number, acknowledgment_number, window, urgent_pointer)
- Flags: SYN, ACK, RST, FIN, URG, PSH
- States: CLOSED, LISTEN, SYN_SENT, SYN_RECEIVED, ESTABLISHED, FIN_WAIT_1, FIN_WAIT_2, CLOSE_WAIT, CLOSING, LAST_ACK, TIME_WAIT

# Predicate Categories
1. Node Predicates:
   - is_tcp_endpoint(x): x is a TCP endpoint
   - is_initiator(x): x is the connection initiator
   - is_responder(x): x is the connection responder

2. Message Predicates:
   - has_sequence_number(m, n): message m has sequence number n
   - has_ack_number(m, n): message m has acknowledgment number n
   - has_window_size(m, w): message m has window size w
   - has_flag(m, f): message m has flag f set
   - is_valid_segment(m): m is a valid TCP segment

3. Action Predicates:
   - sends(x, m, y): node x sends message m to node y
   - receives(x, m, y): node x receives message m from y
   - processes(x, m): node x processes message m
   - retransmits(x, m): node x retransmits message m

4. State Predicates:
   - in_state(x, s): node x is in state s
   - can_transition(s1, s2): state transition from s1 to s2 is valid
   - transitions_to(x, s1, s2): node x transitions from state s1 to s2

5. Relation Predicates:
   - precedes(m1, m2): message m1 precedes message m2
   - acknowledges(m1, m2): message m1 acknowledges message m2
   - belongs_to_connection(m, c): message m belongs to connection c

# State Definitions
- CLOSED: Default state when no connection exists
- LISTEN: Waiting for connection request
- SYN_SENT: Sent connection request, waiting for acknowledgment
- SYN_RECEIVED: Received connection request, sent acknowledgment
- ESTABLISHED: Connection established, data transfer possible
- FIN_WAIT_1: Initiated connection termination
- FIN_WAIT_2: Received ACK of FIN, waiting for FIN from remote
- CLOSE_WAIT: Received FIN, waiting for application to close
- CLOSING: Both sides initiated close simultaneously
- LAST_ACK: Waiting for final ACK after sending FIN
- TIME_WAIT: Waiting to ensure remote TCP received final ACK

# Message Types
1. Connection Establishment:
   - SYN: Initial connection request
   - SYN-ACK: Connection request acknowledgment
   - ACK: Final connection establishment acknowledgment

2. Data Transfer:
   - DATA: Regular data segment
   - ACK: Data acknowledgment

3. Connection Termination:
   - FIN: Connection termination request
   - FIN-ACK: Termination acknowledgment

# Conversion Rules
1. FOL Conversion Rules:
   - Use universal quantifiers (∀) for general rules
   - Use existential quantifiers (∃) for existence claims
   - Use implications (→) for conditional statements
   - Use conjunctions (∧) for multiple conditions
   - Use predicates to express properties and relations
   - Include temporal ordering when relevant
   - Specify state transitions explicitly

2. SMT-LIB Conversion Rules:
   - Declare all sorts and functions at the beginning
   - Use (declare-sort) for types (Node, Message, State, etc.)
   - Use (declare-fun) for predicates
   - Use (assert) for requirements
   - Use (forall) and (exists) for quantifiers
   - Use (=>) for implications
   - Use (and) for conjunctions
   - Use (not) for negations
   - Use (ite) for if-then-else conditions
   - DO NOT include any markdown formatting (no ``` or other markdown)
   - List all predicates used in the conversion
   - Format the SMT-LIB code with proper indentation

# Example Conversions
1. "A SYN segment must have a sequence number."

   FOL:
   ∀m. (has_flag(m, SYN) → ∃n. has_sequence_number(m, n))

   SMT-LIB:
   (declare-sort Message)
   (declare-sort Number)
   (declare-fun has_flag (Message String) Bool)
   (declare-fun has_sequence_number (Message Number) Bool)
   (assert (forall ((m Message))
     (=> (has_flag m "SYN")
         (exists ((n Number))
           (has_sequence_number m n)))))

   Predicates Used:
   - has_flag
   - has_sequence_number

2. "When in CLOSED state, a TCP endpoint must respond to any incoming segment with a RST."

   FOL:
   ∀x,m,y. (is_tcp_endpoint(x) ∧ in_state(x, CLOSED) ∧ receives(x, m, y) →
   ∃r. (has_flag(r, RST) ∧ sends(x, r, y)))

   SMT-LIB:
   (declare-sort Node)
   (declare-sort Message)
   (declare-fun is_tcp_endpoint (Node) Bool)
   (declare-fun in_state (Node String) Bool)
   (declare-fun receives (Node Message Node) Bool)
   (declare-fun has_flag (Message String) Bool)
   (declare-fun sends (Node Message Node) Bool)
   (assert (forall ((x Node) (m Message) (y Node))
     (=> (and (is_tcp_endpoint x)
              (in_state x "CLOSED")
              (receives x m y))
         (exists ((r Message))
           (and (has_flag r "RST")
                (sends x r y))))))

   Predicates Used:
   - is_tcp_endpoint
   - in_state
   - receives
   - has_flag
   - sends

# Task
Convert the given TCP requirement into both First-Order Logic and SMT-LIB format using the predicates and conventions defined above. For each conversion:

1. FOL Conversion:
   - Use appropriate quantifiers
   - Include all relevant conditions
   - Maintain logical consistency
   - Reflect the temporal nature of the protocol (if applicable)
   - Preserve the original meaning of the requirement

2. SMT-LIB Conversion:
   - Declare all necessary sorts and functions
   - Use proper SMT-LIB syntax
   - Ensure all predicates are properly defined
   - Maintain logical equivalence with the FOL conversion
   - Include all necessary assertions
   - List all predicates used in the conversion
   - DO NOT include any markdown formatting
   - Format the SMT-LIB code with proper indentation

3. Explanation:
   - Explain the SMT-LIB conversion in detail
   - Describe how each part of the conversion relates to the original requirement
   - Explain the meaning of each predicate used
   - Describe any assumptions made
""" 