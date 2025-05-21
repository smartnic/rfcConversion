from src.llm import HFLLMConverter
from huggingface_hub import InferenceClient
import re

def test_conversion(rfc_text):
    print(f"\nInput: {rfc_text}")
    converter = HFLLMConverter()
    
    # Get raw response from LLM
    client = InferenceClient(
        token="key",  # Using the default token
        model=converter.client.model
    )
    
    prompt = converter._generate_prompt(rfc_text)
    raw_response = client.text_generation(
        prompt,
        max_new_tokens=150,
        temperature=0.1
    )
    print(f"Raw LLM response: {raw_response}")
    
    # Extract FOL
    fol_match = re.search(r"^([∀∃].*?)(\.|\n|$)", raw_response.strip())
    if fol_match:
        raw_fol = fol_match.group(1).strip()
        print(f"Extracted FOL: {raw_fol}")
        
        # Try validation
        try:
            converter._validate_fol(raw_fol)
            print("Validation successful!")
        except Exception as e:
            print(f"Validation failed: {str(e)}")
    else:
        print("No FOL pattern found in response")
    
    # Try the full extraction method
    try:
        fol = converter.extract_fol(rfc_text)
        print(f"Final output: {fol}")
        print("Conversion successful!")
    except Exception as e:
        print(f"Full conversion failed: {str(e)}")

def main():
    print("Testing FOL Converter...")
    
    # Test with basic example
    test_conversion("The server MUST terminate the connection after 5 failed attempts.")
    
    # Test with more complex examples
    test_conversion("If a client sends more than 3 retransmissions without receiving an ACK, it MUST abort the connection.")
    
    test_conversion("When a server receives a SYN segment, it MUST increment the SYN-RECEIVED counter.")
    
    # New TLS test case
    print("\nTesting new TLS rule...")
    test_conversion("When a TLS server receives a ClientHello message with an unsupported protocol version, it MUST respond with a ProtocolVersion alert and close the connection.")
    
    # Test validation with problematic pattern
    print("\nTesting validation with problematic pattern...")
    converter = HFLLMConverter()
    problematic_fol = "∀s (Server(s) ∧ Count(FailedCount(Attempts,s), 5) → Terminate(s, Connection))"
    try:
        converter._validate_fol(problematic_fol)
        print("Validation passed (should have failed!)")
    except Exception as e:
        print(f"Validation correctly failed: {str(e)}")

if __name__ == "__main__":
    main() 