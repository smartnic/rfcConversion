from setuptools import setup, find_packages

setup(
    name="rfc_analysis",
    version="0.1.0",
    packages=find_packages(),
    install_requires=[
        "z3-solver>=4.14.1.0",
        "spacy>=3.7.2",
        "huggingface-hub>=0.20.3",
        "python-dotenv>=1.0.0",
    ],
    author="Your Name",
    author_email="your.email@example.com",
    description="A tool for analyzing TCP RFC statements and converting them to SMT-LIB/Z3 format",
    long_description=open("README.md").read(),
    long_description_content_type="text/markdown",
    url="https://github.com/yourusername/rfc-to-fol",
    classifiers=[
        "Development Status :: 3 - Alpha",
        "Intended Audience :: Science/Research",
        "License :: OSI Approved :: MIT License",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.8",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
    ],
    python_requires=">=3.8",
) 