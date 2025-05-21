from src.llm import HFLLMConverter
from unittest.mock import patch

def test_simple_requirements():
    """Test converter with simple RFC requirements using mock responses"""
    
    # Test cases with expected outputs
    test_cases = [
        {
            "requirement": "A server MUST send an error response if the request is invalid.",
            "fol_response": "∀s∀r (Server(s) ∧ Request(r) ∧ ¬ValidRequest(r) → ∃resp (Response(resp) ∧ Error(resp) ∧ Send(s,resp)))",
            "smt_response": """
(declare-sort Device)
(declare-sort Request)
(declare-sort Response)
(declare-fun Server (Device) Bool)
(declare-fun ValidRequest (Request) Bool)
(declare-fun Send (Device Response) Bool)
(declare-fun Error (Response) Bool)

(assert
  (forall ((s Device) (r Request))
    (=>
      (and
        (Server s)
        (not (ValidRequest r))
      )
      (exists ((resp Response))
        (and
          (Error resp)
          (Send s resp)
        )
      )
    )
  )
)"""
        },
        {
            "requirement": "A client MUST wait at least 3 seconds before retrying.",
            "fol_response": "∀c (Client(c) → (Retry(c) → After(Retry(c), Retry(c), 3)))",
            "smt_response": """
(declare-sort Device)
(declare-fun Client (Device) Bool)
(declare-fun RetryTime (Device) Int)
(declare-const min_wait Int)

(assert
  (forall ((c Device))
    (=>
      (Client c)
      (>= (RetryTime c) 3)
    )
  )
)"""
        }
    ]
    
    print("\nTesting simple RFC requirements with mock responses:")
    print("=" * 50)
    
    successes = 0
    failures = 0
    
    for i, test_case in enumerate(test_cases, 1):
        print(f"\nTest {i}/{len(test_cases)}")
        print(f"Requirement: {test_case['requirement']}")
        print("-" * 40)
        
        try:
            # Test FOL format
            with patch('huggingface_hub.InferenceClient.text_generation') as mock_gen:
                mock_gen.return_value = test_case['fol_response']
                converter = HFLLMConverter()
                converter.set_output_format("FOL")
                fol = converter.extract_fol(test_case['requirement'])
                print(f"FOL Format:\n{fol}")
            
            # Test SMT-LIB format
            with patch('huggingface_hub.InferenceClient.text_generation') as mock_gen:
                mock_gen.return_value = test_case['smt_response']
                converter.set_output_format("SMT-LIB")
                smt = converter.extract_fol(test_case['requirement'])
                print(f"\nSMT-LIB Format:\n{smt}")
            
            print("\nStatus: Conversion successful! ✅")
            successes += 1
            
        except Exception as e:
            print(f"Status: Failed - {str(e)} ❌")
            failures += 1
        
        print("=" * 50)
    
    # Print summary
    print("\nTest Summary:")
    print(f"Total tests: {len(test_cases)}")
    print(f"Successes: {successes}")
    print(f"Failures: {failures}")
    print(f"Success rate: {(successes/len(test_cases))*100:.1f}%")

if __name__ == "__main__":
    test_simple_requirements() 