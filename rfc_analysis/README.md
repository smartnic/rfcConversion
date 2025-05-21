# RFC to FOL Converter

This project provides tools for converting RFC protocol specifications into First-Order Logic (FOL) representations. The current implementation focuses on TCP (RFC 793) as a case study.

## Project Structure

```
rfc_analysis/
├── src/
│   ├── base_specification.py    # Base class for RFC specifications
│   ├── tcp_specification.py     # TCP-specific implementation
│   └── predicates.py            # Predicate definitions and types
├── examples/
│   └── tcp_examples.py         # Example TCP requirements and FOL
├── tests/                      # Test files
└── data/                       # Data files
```

## Components

### 1. Base Specification (`base_specification.py`)
- Defines the core structure for RFC specifications
- Provides methods for managing nodes, messages, states, and predicates
- Includes validation and transition logic

### 2. TCP Specification (`tcp_specification.py`)
- Implements TCP-specific details from RFC 793
- Defines TCP node types, message formats, and states
- Specifies TCP-specific predicates and actions

### 3. Predicates (`predicates.py`)
- Defines predicate categories and types
- Provides structured representations for:
  - Node predicates
  - Message predicates
  - Action predicates
  - State predicates
  - Relation predicates

### 4. Examples (`tcp_examples.py`)
- Contains example TCP requirements and their FOL representations
- Includes state transitions and message sequences
- Provides explanations for FOL formulas

## Usage

1. Import the necessary components:
```python
from src.tcp_specification import TCPSpecification
from examples.tcp_examples import TCPExample
```

2. Create a TCP specification instance:
```python
tcp_spec = TCPSpecification()
```

3. Access TCP requirements and their FOL representations:
```python
examples = TCPExample.get_examples()
for example in examples:
    print(f"Requirement: {example['requirement']}")
    print(f"FOL: {example['fol']}")
    print(f"Explanation: {example['explanation']}\n")
```

4. View state transitions:
```python
transitions = TCPExample.get_state_transitions()
for from_state, to_state, description in transitions:
    print(f"{from_state} -> {to_state}: {description}")
```

## Example FOL Representations

1. SYN Segment Requirement:
```
∀s (Segment(s) ∧ HasFlag(s,SYN) → ∃n HasSeqNum(s,n))
```

2. CLOSED State Behavior:
```
∀e ∀s (TCPEndpoint(e) ∧ InState(e,CLOSED) ∧ Receive(e,s) → ∃r (Segment(r) ∧ HasFlag(r,RST) ∧ Send(e,r)))
```

3. Three-way Handshake:
```
∃i ∃r ∃s1 ∃s2 ∃s3 (Initiator(i) ∧ Responder(r) ∧ Send(i,s1) ∧ HasFlag(s1,SYN) ∧ Send(r,s2) ∧ HasFlag(s2,SYN) ∧ HasFlag(s2,ACK) ∧ Send(i,s3) ∧ HasFlag(s3,ACK))
```

## Contributing

1. Fork the repository
2. Create a feature branch
3. Commit your changes
4. Push to the branch
5. Create a Pull Request

## License

This project is licensed under the MIT License - see the LICENSE file for details. 