#!/usr/bin/env python3
"""
RFC to FOL Web Interface
Provides a web interface for the RFC to FOL converter.
"""

import os
import json
from flask import Flask, request, jsonify, render_template, send_from_directory
from flask_cors import CORS
from dotenv import load_dotenv
from src.llm import HFLLMConverter

# Load environment variables
load_dotenv()

app = Flask(__name__, static_folder='web/static', template_folder='web/templates')
CORS(app)  # Enable CORS for all routes

# Initialize the converter once for reuse
converter = None
try:
    # Use token from env variable or fall back to default
    hf_token = os.getenv("HUGGINGFACE_TOKEN", "key")
    model_name = os.getenv("DEFAULT_MODEL", "mistralai/Mixtral-8x7B-Instruct-v0.1")
    converter = HFLLMConverter(hf_token=hf_token, model_name=model_name)
except Exception as e:
    print(f"Error initializing converter: {str(e)}")

@app.route('/')
def index():
    """Serve the main page"""
    return render_template('index.html')

@app.route('/convert', methods=['POST'])
def convert():
    """API endpoint to convert RFC text to formal logic"""
    if not converter:
        return jsonify({
            'success': False,
            'error': 'Converter not initialized'
        }), 500
    
    data = request.json
    rfc_text = data.get('rfc_text', '')
    output_format = data.get('output_format', 'FOL').upper()
    model_name = data.get('model', converter.client.model)
    
    if not rfc_text:
        return jsonify({
            'success': False,
            'error': 'RFC text is required'
        }), 400
    
    try:
        # Update model if needed
        if model_name != converter.client.model:
            converter.client.model = model_name
        
        # Set output format
        converter.set_output_format(output_format)
        
        # Convert RFC text to formal logic
        result = converter.extract_fol(rfc_text)
        
        # Generate explanation for FOL
        explanation = {}
        if output_format == 'FOL':
            try:
                explanation = extract_explanation(result)
            except Exception as e:
                explanation = {"error": f"Failed to generate explanation: {str(e)}"}
        
        return jsonify({
            'success': True,
            'rfc_text': rfc_text,
            'result': result,
            'format': output_format,
            'model': model_name,
            'explanation': explanation
        })
        
    except Exception as e:
        return jsonify({
            'success': False,
            'error': str(e)
        }), 500

@app.route('/available_models', methods=['GET'])
def available_models():
    """Return the list of available models"""
    return jsonify({
        'models': HFLLMConverter.available_models()
    })

def extract_explanation(fol):
    """Extract explanation components from FOL formula"""
    explanation = {}
    
    # Check if we have quantifiers
    if fol.startswith("∀") or fol.startswith("∃"):
        # Split by implication
        if "→" in fol:
            parts = fol.split("→")
            explanation["conditions"] = parts[0].strip()
            explanation["actions"] = parts[1].strip()
            
            # Identify variables
            import re
            vars = []
            quantifier_pattern = r'[∀∃]([a-z])'
            for match in re.finditer(quantifier_pattern, fol):
                var = match.group(1)
                if var not in vars:
                    vars.append(var)
            
            explanation["variables"] = vars
    
    return explanation

if __name__ == '__main__':
    port = int(os.environ.get('PORT', 5000))
    from waitress import serve
    print(f"Server is running on http://localhost:{port}")
    serve(app, host='0.0.0.0', port=port) 