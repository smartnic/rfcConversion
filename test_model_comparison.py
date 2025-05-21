#!/usr/bin/env python3
"""
Model Comparison Demo for RFC to FOL Conversion
This script demonstrates the expected behavior of different models using mock responses.
"""

from src.llm import HFLLMConverter
import json
from datetime import datetime
from typing import Dict, List, Any
import sys

# Mock responses for different models
MOCK_RESPONSES = {
    "mistralai/Mixtral-8x7B-Instruct-v0.1": {
        "fol": {
            "simple": "∀s∀r (Server(s) ∧ Request(r) ∧ ¬ValidRequest(r) → ∃resp (Response(resp) ∧ Error(resp) ∧ Send(s,resp)))",
            "http": "∀c∀r (Client(c) ∧ Request(r) ∧ HTTPVersion(r,1.1) → HasHeader(r,Host))",
            "complex": "∀s∀p (Server(s) ∧ Receive(s,p) ∧ HasType(p,SYN) → ∃p2 (Send(s,p2) ∧ HasType(p2,SYN_ACK) ∧ Count(Timer(t), 30)))"
        },
        "smt_lib": {
            "simple": "(declare-sort Device)\n(declare-sort Request)\n(declare-sort Response)\n(declare-fun Server (Device) Bool)\n(declare-fun ValidRequest (Request) Bool)\n(declare-fun Send (Device Response) Bool)\n(declare-fun Error (Response) Bool)\n\n(assert\n  (forall ((s Device) (r Request))\n    (=>\n      (and\n        (Server s)\n        (not (ValidRequest r))\n      )\n      (exists ((resp Response))\n        (and\n          (Error resp)\n          (Send s resp)\n        )\n      )\n    )\n  )\n)"
        }
    },
    "google/gemma-7b-it": {
        "fol": {
            "simple": "∀s∀r (Server(s) ∧ Request(r) ∧ ¬ValidRequest(r) → ∃resp (Response(resp) ∧ Error(resp) ∧ Send(s,resp)))",
            "http": "∀c∀r (Client(c) ∧ Request(r) ∧ HTTPVersion(r,1.1) → HasHeader(r,Host))",
            "complex": "∀s∀p (Server(s) ∧ Receive(s,p) ∧ HasType(p,SYN) → ∃p2 (Send(s,p2) ∧ HasType(p2,SYN_ACK) ∧ Count(Timer(t), 30)))"
        },
        "smt_lib": {
            "simple": "(declare-sort Device)\n(declare-sort Request)\n(declare-sort Response)\n(declare-fun Server (Device) Bool)\n(declare-fun ValidRequest (Request) Bool)\n(declare-fun Send (Device Response) Bool)\n(declare-fun Error (Response) Bool)\n\n(assert\n  (forall ((s Device) (r Request))\n    (=>\n      (and\n        (Server s)\n        (not (ValidRequest r))\n      )\n      (exists ((resp Response))\n        (and\n          (Error resp)\n          (Send s resp)\n        )\n      )\n    )\n  )\n)"
        }
    },
    "NousResearch/Nous-Hermes-2-Mixtral-8x7B-DPO": {
        "fol": {
            "simple": "∀s∀r (Server(s) ∧ Request(r) ∧ ¬ValidRequest(r) → ∃resp (Response(resp) ∧ Error(resp) ∧ Send(s,resp)))",
            "http": "∀c∀r (Client(c) ∧ Request(r) ∧ HTTPVersion(r,1.1) → HasHeader(r,Host))",
            "complex": "∀s∀p (Server(s) ∧ Receive(s,p) ∧ HasType(p,SYN) → ∃p2 (Send(s,p2) ∧ HasType(p2,SYN_ACK) ∧ Count(Timer(t), 30)))"
        },
        "smt_lib": {
            "simple": "(declare-sort Device)\n(declare-sort Request)\n(declare-sort Response)\n(declare-fun Server (Device) Bool)\n(declare-fun ValidRequest (Request) Bool)\n(declare-fun Send (Device Response) Bool)\n(declare-fun Error (Response) Bool)\n\n(assert\n  (forall ((s Device) (r Request))\n    (=>\n      (and\n        (Server s)\n        (not (ValidRequest r))\n      )\n      (exists ((resp Response))\n        (and\n          (Error resp)\n          (Send s resp)\n        )\n      )\n    )\n  )\n)"
        }
    },
    "01-ai/Yi-34B-Chat": {
        "fol": {
            "simple": "∀s∀r (Server(s) ∧ Request(r) ∧ ¬ValidRequest(r) → ∃resp (Response(resp) ∧ Error(resp) ∧ Send(s,resp)))",
            "http": "∀c∀r (Client(c) ∧ Request(r) ∧ HTTPVersion(r,1.1) → HasHeader(r,Host))",
            "complex": "∀s∀p (Server(s) ∧ Receive(s,p) ∧ HasType(p,SYN) → ∃p2 (Send(s,p2) ∧ HasType(p2,SYN_ACK) ∧ Count(Timer(t), 30)))"
        },
        "smt_lib": {
            "simple": "(declare-sort Device)\n(declare-sort Request)\n(declare-sort Response)\n(declare-fun Server (Device) Bool)\n(declare-fun ValidRequest (Request) Bool)\n(declare-fun Send (Device Response) Bool)\n(declare-fun Error (Response) Bool)\n\n(assert\n  (forall ((s Device) (r Request))\n    (=>\n      (and\n        (Server s)\n        (not (ValidRequest r))\n      )\n      (exists ((resp Response))\n        (and\n          (Error resp)\n          (Send s resp)\n        )\n      )\n    )\n  )\n)"
        }
    }
}

def demonstrate_model(model_name: str, test_cases: List[Dict[str, str]], output_format: str = "FOL"):
    """Demonstrate a model's capabilities using mock responses"""
    print(f"\n{'='*80}")
    print(f"Model: {model_name}")
    print(f"Output format: {output_format}")
    print(f"{'='*80}")
    
    results = {
        "model": model_name,
        "format": output_format,
        "timestamp": datetime.now().isoformat(),
        "test_cases": []
    }
    
    for i, case in enumerate(test_cases, 1):
        print(f"\nTest Case {i}/{len(test_cases)}")
        print(f"Requirement: {case['requirement']}")
        print("-" * 40)
        
        # Get mock response
        mock_response = MOCK_RESPONSES[model_name][output_format.lower()][case['category']]
        
        case_result = {
            "requirement": case['requirement'],
            "output": mock_response,
            "success": True,
            "time_seconds": 0.5  # Mock time
        }
        
        results["test_cases"].append(case_result)
        
        print(f"Output:\n{mock_response}")
        print(f"Status: Success (0.50s) ✅")
    
    return results

def main():
    # Test cases with varying complexity
    test_cases = [
        # Simple cases
        {
            "requirement": "A server MUST send an error response if the request is invalid.",
            "category": "simple"
        },
        {
            "requirement": "A client MUST wait at least 3 seconds before retrying.",
            "category": "simple"
        },
        # HTTP-specific cases
        {
            "requirement": "A client MUST send a Host header field in all HTTP/1.1 request messages.",
            "category": "http"
        },
        {
            "requirement": "A server MUST respond with a 400 (Bad Request) status code to any HTTP/1.1 request message that lacks a Host header field.",
            "category": "http"
        },
        # Complex cases
        {
            "requirement": "When a server receives a SYN segment, it MUST increment the SYN-RECEIVED counter and respond with a SYN-ACK within 30 seconds.",
            "category": "complex"
        },
        {
            "requirement": "If a server receives 3 failed attempts, it MUST close the connection and wait for 5 minutes before accepting new connections.",
            "category": "complex"
        }
    ]
    
    all_results = []
    
    # Test each model
    for model_name in MOCK_RESPONSES.keys():
        try:
            # Test FOL format
            fol_results = demonstrate_model(model_name, test_cases, "FOL")
            all_results.append(fol_results)
            
            # Test SMT-LIB format
            smt_results = demonstrate_model(model_name, test_cases, "SMT-LIB")
            all_results.append(smt_results)
            
        except Exception as e:
            print(f"Error demonstrating model {model_name}: {str(e)}")
            continue
    
    # Save results to file
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    filename = f"model_comparison_demo_{timestamp}.json"
    
    with open(filename, 'w') as f:
        json.dump(all_results, f, indent=2)
    
    # Print summary
    print("\nTest Summary:")
    print(f"Results saved to: {filename}")
    
    for result in all_results:
        model = result["model"]
        format_type = result["format"]
        total_cases = len(result["test_cases"])
        successful_cases = sum(1 for case in result["test_cases"] if case["success"])
        avg_time = sum(case["time_seconds"] for case in result["test_cases"]) / total_cases if total_cases > 0 else 0
        
        print(f"\nModel: {model}")
        print(f"Format: {format_type}")
        print(f"Success rate: {(successful_cases/total_cases)*100:.1f}%")
        print(f"Average time per case: {avg_time:.2f}s")
        
        # Print model-specific analysis
        print("\nModel Analysis:")
        if "mistralai" in model:
            print("- Strengths: Good at complex protocol rules, accurate FOL conversion")
            print("- Weaknesses: Slightly slower processing time")
        elif "gemma" in model:
            print("- Strengths: Fast processing, good at simple rules")
            print("- Weaknesses: May struggle with complex temporal logic")
        elif "nous" in model:
            print("- Strengths: Good balance of speed and accuracy")
            print("- Weaknesses: May need more context for complex rules")
        elif "yi" in model:
            print("- Strengths: Excellent at complex rules, good at temporal logic")
            print("- Weaknesses: Higher resource requirements")

if __name__ == "__main__":
    main() 