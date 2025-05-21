#!/usr/bin/env python3
"""
Simple starter script for the RFC to FOL web interface.
"""

import os
import sys
import webbrowser
import subprocess
import time
import platform

def install_requirements():
    print("Checking and installing requirements...")
    try:
        subprocess.check_call([sys.executable, "-m", "pip", "install", "-r", "requirements.txt"])
        print("Requirements installed successfully.")
        return True
    except subprocess.CalledProcessError:
        print("Error installing requirements. Please install them manually: pip install -r requirements.txt")
        return False

def start_server():
    print("Starting the web server...")
    print("The web interface will be available at: http://localhost:5000")
    
    # Start the server process
    server_process = subprocess.Popen([sys.executable, "web_app.py"])
    
    # Wait a bit for the server to start
    time.sleep(2)
    
    # Open the web browser
    print("Opening web browser...")
    webbrowser.open("http://localhost:5000")
    
    print("\nPress Ctrl+C to stop the server when you're done.")
    try:
        # Keep the script running until KeyboardInterrupt
        server_process.wait()
    except KeyboardInterrupt:
        print("\nShutting down the server...")
        server_process.terminate()
        server_process.wait()
        print("Server stopped. Goodbye!")

if __name__ == "__main__":
    print("=" * 60)
    print("RFC to FOL Converter - Web Interface Starter")
    print("=" * 60)
    
    if install_requirements():
        start_server() 