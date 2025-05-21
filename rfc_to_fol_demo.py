#!/usr/bin/env python3
"""
RFC to FOL Converter Demo
This script demonstrates the usage of the RFC to FOL converter with different output formats.
"""

from src.llm import HFLLMConverter
import argparse
import re

def main():
    parser = argparse.ArgumentParser(description="Convert RFC rules to formal logic")
    parser.add_argument("--format", choices=["fol", "smt-lib"], default="fol",
                        help="Output format (FOL or SMT-LIB)")
    parser.add_argument("--model", default="mistralai/Mixtral-8x7B-Instruct-v0.1",
                        help="HuggingFace model to use")
    parser.add_argument("--list-models", action="store_true", 
                        help="List available recommended models")
    parser.add_argument("--token", default=None,
                        help="HuggingFace API token (optional, will use default if not provided)")
    parser.add_argument("--rfc", 
                        help="RFC rule to convert")
    parser.add_argument("--interactive", action="store_true",
                        help="Run in interactive mode")
    
    args = parser.parse_args()
    
    # List available models if requested
    if args.list_models:
        print("Recommended models for RFC to FOL conversion:")
        for model in HFLLMConverter.available_models():
            print(f"  - {model}")
        return
    
    # Initialize converter
    token = args.token or "key"
    try:
        converter = HFLLMConverter(hf_token=token, model_name=args.model)
        converter.set_output_format(args.format)
        print(f"Using model: {args.model}")
        print(f"Output format: {args.format.upper()}")
    except Exception as e:
        print(f"Error initializing converter: {str(e)}")
        return
    
    # Process a single rule if provided
    if args.rfc:
        process_rule(converter, args.rfc)
        return
    
    # Interactive mode
    if args.interactive:
        print("\n=== RFC to FOL Converter ===")
        print("Enter RFC rules to convert them to formal logic.")
        print("Type 'quit' or 'exit' to end the session.\n")
        
        while True:
            try:
                rfc_rule = input("\nEnter RFC rule: ")
                if rfc_rule.lower() in ["quit", "exit", "q"]:
                    break
                if not rfc_rule.strip():
                    continue
                
                process_rule(converter, rfc_rule)
            except KeyboardInterrupt:
                print("\nExiting...")
                break
        return
    
    # If no rule or interactive mode, show an example
    example_rule = "When a server receives a SYN segment, it MUST increment the SYN-RECEIVED counter."
    print("\nNo rule provided. Demonstrating with an example:")
    print(f"Example rule: {example_rule}")
    process_rule(converter, example_rule)
    print("\nUse --rfc to specify a rule or --interactive for interactive mode")

def process_rule(converter, rfc_rule):
    print(f"\nInput: {rfc_rule}")
    try:
        result = converter.extract_fol(rfc_rule)
        print("\nConverted to formal logic:")
        print(result)
        
        # Add explanation for FOL format
        if converter.output_format == "FOL":
            explain_fol(result)
    except Exception as e:
        print(f"Error: {str(e)}")

def explain_fol(fol):
    """Provide a simple explanation of the FOL formula"""
    # Extract the main structure
    try:
        # Check if we have quantifiers
        if fol.startswith("∀") or fol.startswith("∃"):
            print("\nExplanation:")
            
            # Split by implication
            if "→" in fol:
                parts = fol.split("→")
                conditions = parts[0].strip()
                actions = parts[1].strip()
                
                print(f"- Conditions: {conditions}")
                print(f"- Actions: {actions}")
                
                # Identify variables - better approach
                # Extract variables from quantifiers
                vars = []
                quantifier_pattern = r'[∀∃]([a-z])'
                for match in re.finditer(quantifier_pattern, fol):
                    var = match.group(1)
                    if var not in vars:
                        vars.append(var)
                
                if vars:
                    print(f"- Variables: {', '.join(vars)}")
            else:
                print("- Formula doesn't follow the standard condition → action format")
    except Exception:
        # If parsing fails, don't provide explanation
        pass

if __name__ == "__main__":
    main() 