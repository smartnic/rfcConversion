from src.llm import HFLLMConverter
import time
import json
from datetime import datetime

def test_model_with_examples(model_name, examples, output_format="FOL"):
    """Test a specific model with a set of RFC examples"""
    print(f"\n--- Testing model: {model_name} with {output_format} format ---")
    
    results = {
        "model": model_name,
        "format": output_format,
        "timestamp": datetime.now().isoformat(),
        "examples": []
    }
    
    try:
        converter = HFLLMConverter(model_name=model_name)
        converter.set_output_format(output_format)
        
        for i, example in enumerate(examples):
            print(f"\nExample {i+1}: {example}")
            start_time = time.time()
            
            try:
                result = converter.extract_fol(example)
                success = True
                error = None
            except Exception as e:
                result = None
                success = False
                error = str(e)
            
            elapsed_time = time.time() - start_time
            
            example_result = {
                "input": example,
                "output": result,
                "success": success,
                "error": error,
                "time_seconds": elapsed_time
            }
            
            results["examples"].append(example_result)
            
            if success:
                print(f"✅ Success ({elapsed_time:.2f}s)")
                print(f"Output: {result}")
            else:
                print(f"❌ Failed ({elapsed_time:.2f}s): {error}")
                
    except Exception as e:
        print(f"Model initialization error: {str(e)}")
        results["initialization_error"] = str(e)
    
    # Save results to file
    filename = f"results_{model_name.split('/')[-1]}_{output_format.lower()}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    with open(filename, 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"\nResults saved to {filename}")
    return results

def main():
    # Test examples covering various RFC rule patterns
    examples = [
        "The server MUST terminate the connection after 5 failed attempts.",
        "If a client sends more than 3 retransmissions without receiving an ACK, it MUST abort the connection.",
        "When a server receives a SYN segment, it MUST increment the SYN-RECEIVED counter.",
        "Packets with the RST bit set SHOULD be silently discarded.",
        "If the server receives an ACK with an invalid sequence number, it MUST respond with a RST packet.",
        "A TCP receiver SHOULD NOT shrink its window, and MUST not shrink the right window edge.",
        "A TCP implementation MUST be robust against wrapped sequence numbers."
    ]
    
    # Model to test (a subset of available models to save time)
    models_to_test = [
        "mistralai/Mixtral-8x7B-Instruct-v0.1",  # Current default
        "google/gemma-7b-it",  # Good instruction following
    ]
    
    # Test FOL output for each model
    all_results = []
    for model in models_to_test:
        results = test_model_with_examples(model, examples, "FOL")
        all_results.append(results)
    
    # Test SMT-LIB output with the best model (based on FOL results)
    best_model = models_to_test[0]  # Default to first model, can be modified based on results
    smt_results = test_model_with_examples(best_model, examples[:3], "SMT-LIB")  # Test with just 3 examples
    all_results.append(smt_results)
    
    print("\n--- Testing complete ---")
    # Print a simple summary
    print("\nSummary of success rates:")
    for result in all_results:
        success_count = sum(1 for ex in result["examples"] if ex["success"])
        total = len(result["examples"])
        print(f"{result['model']} ({result['format']}): {success_count}/{total} successful conversions")

if __name__ == "__main__":
    main() 