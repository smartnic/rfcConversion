import re

def validate_fol(fol_str):
    """
    Validates FOL syntax using regex patterns.
    Checks for:
    - Quantifiers (∀/∃) with variables
    - Proper parentheses
    - Valid predicate structure
    - Logical operators (→, ∧, ∨, ¬)
    """
    # Normalize whitespace
    fol_str = fol_str.strip().replace(" ", "")
    
    # Base pattern components
    var = r"[a-z]"          # Single lowercase variable
    vars = r"[a-z]+"        # Multiple variables (for predicates)
    predicate = r"\w+\([a-z,]*\)"  # Predicate like P(x) or Q(x,y)
    
    # Atomic formula can be predicate or negation
    atom = rf"({predicate}|¬{predicate})"
    
    # Logical connectives
    connective = r"(→|∧|∨)"
    
    # Full pattern
    pattern = rf"""
        ^                           # Start of string
        [∀∃]{var}                   # Quantifier with variable
        \(                          # Opening paren for scope
            (                       # Body consists of:
                {atom}              # Atomic formula
                ({connective}{atom})*  # Optional connectives + atoms
            |                       # OR
                \(.+\)              # Nested parentheses
            )
        \)                          # Closing paren
        $                           # End of string
    """.replace("\n", "").replace(" ", "")

    return re.fullmatch(pattern, fol_str) is not None

# Example usage
if __name__ == "__main__":
    test_cases = [
        ("∀s(FailedAttempts(s,5)→TerminateConnection(s)", True),
        ("∀x(P(x)∧Q(x))", False),  # Extra closing paren
        ("∃y(¬R(y)∨S(y))", True),
        ("∀xP(x)→Q(x)", False),    # Missing parens around implication
    ]
    
    for fol, expected in test_cases:
        result = validate_fol(fol)
        print(f"'{fol}': {'Valid' if result else 'Invalid'}")
        assert result == expected