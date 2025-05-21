def get_tcp_rfc_prompt():
    """Generate a TCP-specific prompt for converting RFC 793 requirements to FOL"""
    return f"""
You are an expert in converting TCP protocol specifications (RFC 793) into First-Order Logic (FOL) representations.
Your task is to convert natural language requirements from RFC 793 into formal FOL expressions.

# TCP Protocol Elements

## Object Typing (Nodes and Entities)
- TCPEndpoint(t): t is a TCP endpoint
- Client(c): c is a client node (initiator of a connection)
- Server(s): s is a server node (listener for incoming connections)
- Segment(m): m is a TCP segment
- Field(f): f is a field in a TCP segment
- Timer(t): t is a timer
- State(s): s is a TCP state

## Message Content Predicates
- Segment(m): m is a TCP segment
- SYN(m): m is a SYN segment (connection initiation)
- ACK(m): m is an ACK segment (acknowledgment)
- RST(m): m is a RST segment (reset)
- FIN(m): m is a FIN segment (finish)
- SequenceNumber(m, n): segment m carries sequence number n
- ValidSequenceNumber(n): n is a valid sequence number
- BitLength(n, k): number n is represented in k bits
- UrgentPointer(m, u): segment m contains urgent pointer u
- Window(m, w): segment m contains window field w
- FieldInSegment(f, m): field f is part of segment m
- IdentifiesFirstOctet(f, o): field f identifies the first data octet o
- HasBitLength(f, n): field f has a bit length of n

## Node Action Predicates
- Send(x, m): node x sends segment m
- Receive(x, m): node x receives segment m
- Ignore(x, m): node x ignores segment m
- SentBy(x, m): node x sends segment m
- Retransmit(t, m): TCP implementation t retransmits segment m
- TimerExpired(t): timer t has expired
- TimerStarted(t, m): timer t is started for segment m
- AcknowledgmentReceived(m): segment m has been acknowledged

## Inter-Message Relationship Predicates
- Response(r, m): segment r is a response to segment m
- ThreeWayHandshake(c, s): valid three-way handshake completed between client c and server s
- ConnectionEstablished(c, s): connection is established between client c and server s
- ExchangesMessage(c, s, m): client c and server s exchange message m
- Precedes(m1, m2): segment m1 precedes segment m2 in time
- LastDataOctet(m, n): segment m contains the last data octet with sequence number n

## TCP State Machine Predicates
- InState(t, s): TCP endpoint t is in state s
- TransitionsTo(t, s1, s2): TCP endpoint t transitions from state s1 to s2
- ValidTransition(s1, s2): transition from state s1 to s2 is valid
- LISTEN: TCP endpoint is in LISTEN state
- SYN_SENT: TCP endpoint is in SYN_SENT state
- SYN_RECEIVED: TCP endpoint is in SYN_RECEIVED state
- ESTABLISHED: TCP endpoint is in ESTABLISHED state

# Example Conversions

1. State-based Behavior:
   "A TCP endpoint in LISTEN state must ignore RST segments."
   FOL: ∀t,m. (TCPEndpoint(t) ∧ InState(t, LISTEN) ∧ RST(m)) → Ignore(t, m)
   
2. Connection Establishment:
   "A TCP connection is established by the exchange of a SYN, a SYN-ACK, and an ACK."
   FOL: ∀c,s. ConnectionEstablished(c, s) ↔ 
        ∃m1,m2,m3. (SYN(m1) ∧ SYN(m2) ∧ ACK(m2) ∧ ACK(m3) ∧
        Send(c, m1) ∧ Receive(s, m1) ∧
        Send(s, m2) ∧ Receive(c, m2) ∧
        Send(c, m3) ∧ Receive(s, m3))

3. Timer-based Retransmission:
   "If no acknowledgment is received before the timer expires, the segment is retransmitted."
   FOL: ∀t,m. (TimerExpired(t) ∧ TimerStarted(t, m) ∧ ¬AcknowledgmentReceived(m)) → Retransmit(t, m)

# FOL Syntax Guide
- ∀x: for all x
- ∃x: there exists x
- ∧: and
- ∨: or
- →: implies
- ↔: if and only if
- ¬: not
- (): grouping

# Task
Convert the following TCP requirement from RFC 793 into FOL:

[TCP Requirement]

# Guidelines
1. Identify all relevant predicates from the categories above
2. Use appropriate quantifiers (∀, ∃) for each variable
3. Express the requirement using logical operators (∧, ∨, →, ¬)
4. Ensure the FOL representation captures all aspects of the requirement
5. Use clear variable names that reflect their meaning
6. Group related predicates using parentheses
7. Include an explanation of your FOL representation

# Output Format
Provide your response in the following format:

FOL:
[Your FOL expression]

Explanation:
[Explanation of how the FOL captures the requirement]
""" 