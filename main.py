from src.llm import HFLLMConverter

converter = HFLLMConverter(hf_token="key")
sentence = "The server MUST terminate the connection after 5 failed attempts."
fol = converter.extract_fol(sentence)
print(fol)  # Output: ∀s (FailedAttempts(s, 5) → TerminateConnection(s))