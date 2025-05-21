# RFC to FOL (First-Order Logic) Converter

A tool for analyzing TCP RFC statements and converting them to SMT-LIB/Z3 format for formal verification.

## Features

- Converts TCP RFC statements to SMT-LIB format
- Supports Z3 solver integration for formal verification
- Provides detailed analysis of TCP protocol specifications
- Includes test suite for verification of conversions

## Installation

1. Clone the repository:
```bash
git clone https://github.com/yourusername/rfc-to-fol.git
cd rfc-to-fol
```

2. Create a virtual environment and activate it:
```bash
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate
```

3. Install the package:
```bash
pip install -e .
```

## Usage

### Basic Usage

```python
from rfc_analysis.src.converter import RFCConverter
from rfc_analysis.src.generators.smtlib_generator import SMTLibGenerator

# Create a converter instance
converter = RFCConverter()

# Convert an RFC statement
statement = "If a TCP segment arrives with a sequence number that is less than the expected sequence number, the segment should be discarded."
smtlib_expr = converter.convert_to_smtlib(statement)

# Generate SMT-LIB code
generator = SMTLibGenerator()
smtlib_code = generator.generate(smtlib_expr)
```

### Using Z3 for Verification

```python
from rfc_analysis.src.generators.z3_generator import Z3Generator
from z3 import *

# Create a Z3 generator instance
generator = Z3Generator()

# Generate and verify Z3 expressions
result = generator.verify_statement(statement)
print(f"Verification result: {result}")
```

## Project Structure

```
rfc_analysis/
├── src/
│   ├── generators/
│   │   ├── smtlib_generator.py
│   │   └── z3_generator.py
│   ├── prompts/
│   │   ├── tcp_rfc_prompt.py
│   │   └── detailed_conversion_prompt.md
│   ├── converter.py
│   └── llm.py
├── tests/
│   ├── test_smtlib_generator.py
│   ├── test_z3_generator.py
│   └── test_chatgpt_comparison.py
├── docs/
├── examples/
├── setup.py
└── requirements.txt
```

## Testing

Run the test suite:
```bash
python -m pytest tests/
```

## Contributing

1. Fork the repository
2. Create a feature branch
3. Commit your changes
4. Push to the branch
5. Create a Pull Request

## Credit

This project was made by Rudraksh Simlote for Independent Study at Rutgers University under Professor Srinivas Narayana.

## Acknowledgments

- Z3 Theorem Prover
- TCP RFC Specifications
- Hugging Face Transformers 
