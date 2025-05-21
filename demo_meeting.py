#!/usr/bin/env python3
"""
RFC to FOL/SMT-LIB Converter Demo for Research Meeting
This script demonstrates the improvements made to the converter with specific RFC examples.
"""

from src.llm import HFLLMConverter
import json
from datetime import datetime

def run_demo(converter, rfc_text, format_type):
    print(f"\n{'='*80}")
    print(f"Testing {format_type} conversion for RFC rule:")
    print(f"Input: {rfc_text}")
    print(f"{'='*80}")
    
    try:
        converter.set_output_format(format_type)
        result = converter.extract_fol(rfc_text)
        print(f"\n{format_type} Output:")
        print(result)
        return True, result
    except Exception as e:
        print(f"Error: {str(e)}")
        return False, str(e)

def main():
    # Initialize converter
    converter = HFLLMConverter()
    
    # RFC examples from different protocols
    examples = [
        # TCP Example (RFC 9293)
        {
            "protocol": "TCP",
            "rule": "When a server receives a SYN segment, it MUST increment the SYN-RECEIVED counter and respond with a SYN-ACK within 30 seconds.",
            "source": "RFC 9293"
        },
        # TLS Example (RFC 8446)
        {
            "protocol": "TLS",
            "rule": "When a TLS server receives a ClientHello message with an unsupported protocol version, it MUST respond with a ProtocolVersion alert and close the connection.",
            "source": "RFC 8446"
        },
        # HTTP Example (RFC 7230)
        {
            "protocol": "HTTP",
            "rule": "An HTTP/1.1 server MUST respond with a 400 (Bad Request) status code to any HTTP/1.1 request that lacks a Host header field.",
            "source": "RFC 7230"
        }
    ]
    
    results = []
    
    for example in examples:
        print(f"\nTesting {example['protocol']} rule from {example['source']}")
        
        # Test FOL conversion
        fol_success, fol_result = run_demo(converter, example['rule'], "FOL")
        
        # Test SMT-LIB conversion
        smt_success, smt_result = run_demo(converter, example['rule'], "SMT-LIB")
        
        results.append({
            "protocol": example['protocol'],
            "source": example['source'],
            "rule": example['rule'],
            "fol": {
                "success": fol_success,
                "result": fol_result
            },
            "smt_lib": {
                "success": smt_success,
                "result": smt_result
            }
        })
    
    # Save results to file
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    filename = f"demo_results_{timestamp}.json"
    with open(filename, 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"\nResults saved to {filename}")

if __name__ == "__main__":
    main() 