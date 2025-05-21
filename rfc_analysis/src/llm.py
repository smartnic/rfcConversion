from huggingface_hub import InferenceClient
import re

class HFLLMConverter:
    def __init__(self, hf_token="key", model_name="mistralai/Mixtral-8x7B-Instruct-v0.1"):
        self.client = InferenceClient(
            token=hf_token,
            model=model_name
        )
        # Default output format
        self.output_format = "FOL"  # Options: "FOL", "SMT-LIB"
    
    def set_output_format(self, format_type):
        """Set the output format (FOL or SMT-LIB)"""
        if format_type.upper() not in ["FOL", "SMT-LIB"]:
            raise ValueError("Format must be either 'FOL' or 'SMT-LIB'")
        self.output_format = format_type.upper()
    
    def extract_fol(self, rfc_text, max_retries=3):
        """Extract FOL with retries on validation failure"""
        last_error = None
        
        for attempt in range(max_retries):
            try:
                response = self.client.text_generation(
                    self._generate_prompt(rfc_text),
                    max_new_tokens=300,  # Increased for SMT-LIB which can be verbose
                    temperature=0.1 * (attempt + 1),  # Slightly increase temperature on retries
                    do_sample=attempt > 0  # Use sampling after first attempt
                )
                
                # Clean up the response
                response = response.strip()
                
                if self.output_format == "FOL":
                    # Extract FOL formula
                    fol_match = re.search(r"^([∀∃].*?)(\.|\n|$)", response)
                    if not fol_match:
                        raise ValueError("No valid FOL formula found in response")
                    
                    fol = fol_match.group(1).strip()
                    
                    # Validate FOL
                    self._validate_fol(fol)
                    return fol
                else:  # SMT-LIB format
                    # Extract SMT-LIB code
                    smt_lib_match = re.search(r"\(.*\)", response, re.DOTALL)
                    if not smt_lib_match:
                        raise ValueError("No valid SMT-LIB expression found in response")
                    
                    smt_lib = smt_lib_match.group(0).strip()
                    
                    # Validate SMT-LIB
                    self._validate_smt_lib(smt_lib)
                    return smt_lib
                
            except Exception as e:
                last_error = str(e)
                continue
        
        raise Exception(f"Failed to generate valid output after {max_retries} attempts. Last error: {last_error}")

    def _generate_prompt(self, rfc_text):
        """Generate the prompt for the LLM to convert RFC text to FOL or SMT-LIB"""
        if self.output_format == "FOL":
            return self._generate_fol_prompt(rfc_text)
        else:
            return self._generate_smt_lib_prompt(rfc_text)
    
    def _generate_fol_prompt(self, rfc_text):
        """Generate prompt for FOL conversion"""
        return f"""Convert this RFC networking protocol rule into First-Order Logic (FOL). Output ONLY the FOL formula with no additional text.

Rule: "{rfc_text}"

Guidelines:
1. Use standard FOL notation:
   - ∀ (universal), ∃ (existential)
   - ∧ (and), ∨ (or), → (implies), ¬ (not)
   - ( ) for grouping
   - =, <, >, ≤, ≥ for relations

2. Predicate Categories:
   a) Entity: Client(c), Server(s), Message(m), Header(h)
   b) Action: Send(s,m), Receive(r,m), Process(p,m)
   c) State: Connected(s,c), Established(c), HandshakeComplete(h)
   d) Property: Valid(m), Malformed(h), Complete(p)

3. Protocol-Specific:
   HTTP: HTTPRequest(r), HostHeader(h), Method(m,type)
   TCP: TCPSegment(s), SYN(s), SequenceNumber(n)
   TLS: TLSSession(s), CipherSuite(c), KeyExchange(k)

4. Formula Patterns:
   a) Universal: ∀x (X(x) → Y(x))
   b) Existential: ∃x (X(x) ∧ Y(x))
   c) Conditional: ∀x (X(x) → Y(x))
   d) Temporal: ∀x (X(x) → ∃y (Y(y) ∧ After(x,y)))

Examples:
1. Simple MUST:
Input: "A server MUST send an error response if the request is invalid."
Output: ∀s∀r (Server(s) ∧ Request(r) ∧ ¬ValidRequest(r) → ∃resp (Response(resp) ∧ Error(resp) ∧ Send(s,resp)))

2. Conditional:
Input: "If a client sends more than 3 retransmissions without receiving an ACK, it MUST abort the connection."
Output: ∀c∀r (Client(c) ∧ Retransmissions(r) ∧ Count(r) > 3 ∧ ¬ReceivedACK(c,r) → ∃a (Abort(a) ∧ Connection(c) ∧ Perform(c,a)))

3. Temporal:
Input: "After receiving a SYN, the server MUST send a SYN-ACK."
Output: ∀s∀syn (Server(s) ∧ SYN(syn) ∧ Receive(s,syn) → ∃sa (SYNACK(sa) ∧ Send(s,sa)))

Now convert this:
Input: "
Output:"""

    def _generate_smt_lib_prompt(self, rfc_text):
        """Generate prompt for SMT-LIB conversion"""
        return f"""Convert this RFC networking protocol rule into SMT-LIB format. Output ONLY the SMT-LIB expression with no additional text.

Rule: "{rfc_text}"

Guidelines:
1. Sort Declarations:
   (declare-sort Client 0)
   (declare-sort Server 0)
   (declare-sort Message 0)
   (declare-sort Header 0)

2. Function Categories:
   a) Entity: (declare-fun Client (Client) Bool)
   b) Action: (declare-fun Send (Server Message) Bool)
   c) State: (declare-fun Connected (Server Connection) Bool)
   d) Property: (declare-fun Valid (Message) Bool)

3. Protocol-Specific:
   HTTP: (declare-sort HTTPRequest 0), (declare-fun HostHeader (Header) Bool)
   TCP: (declare-sort TCPSegment 0), (declare-fun SYN (TCPSegment) Bool)
   TLS: (declare-sort TLSSession 0), (declare-fun CipherSuite (TLSSession) Bool)

Examples:
1. Simple MUST:
Input: "A server MUST send an error response if the request is invalid."

Output:
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
)

2. Conditional:
Input: "If a client sends more than 3 retransmissions without receiving an ACK, it MUST abort the connection."

Output:
(declare-sort Device)
(declare-sort Connection)
(declare-sort Retransmission)
(declare-fun Client (Device) Bool)
(declare-fun Retransmissions (Device Retransmission) Bool)
(declare-fun Count (Retransmission Int) Bool)
(declare-fun ReceivedACK (Device Retransmission) Bool)
(declare-fun Abort (Device Connection) Bool)

(assert
  (forall ((c Device) (r Retransmission))
    (=>
      (and
        (Client c)
        (Retransmissions c r)
        (> (Count r) 3)
        (not (ReceivedACK c r))
      )
      (exists ((conn Connection))
        (Abort c conn)
      )
    )
  )
)

Now convert this:
Input: "
Output:"""

    def _validate_fol(self, fol):
        """Simple validation of FOL formula structure"""
        # Check for basic formula structure
        if not re.match(r'^[∀∃]', fol):
            raise ValueError("Formula must start with a quantifier (∀/∃)")
            
        # Check balanced parentheses
        if fol.count('(') != fol.count(')'):
            raise ValueError("Unbalanced parentheses in formula")
            
        # Check for required logical operators
        if '→' not in fol:
            raise ValueError("Formula must contain an implication (→)")
            
        # Check for common predicates
        standard_predicates = [
            'Server', 'Client', 'Packet', 'Send', 'Receive',
            'HTTPVersion', 'HasHeader', 'HasHeaderValue', 'HasAuthority',
            'CountHeaders', 'ValidHeaderValue', 'EmptyValue'
        ]
        if not any(pred in fol for pred in standard_predicates):
            raise ValueError("Formula must use standard predicates")
            
        # Specifically check for the problematic pattern
        if 'Count(FailedCount(Attempts' in fol:
            raise ValueError("Invalid counter format. Use Count(FailedAttempts(s), n) instead of Count(FailedCount(Attempts,s), n)")
            
        # HTTP-specific validations
        if 'HTTPVersion' in fol and 'Host' in fol:
            # Check for proper HTTP version format
            if not re.search(r'HTTPVersion\([^,]+,\s*[0-9]+\.[0-9]+\)', fol):
                raise ValueError("Invalid HTTP version format")
            
            # Check for proper Host header predicates
            if 'HasHeader' in fol and not re.search(r'HasHeader\([^,]+,\s*Host\)', fol):
                raise ValueError("Invalid Host header predicate format")
            
            # Check for proper header value format
            if 'HasHeaderValue' in fol and not re.search(r'HasHeaderValue\([^,]+,\s*Host,\s*[^)]+\)', fol):
                raise ValueError("Invalid Host header value format")
    
    def _validate_smt_lib(self, smt_lib):
        """Validate SMT-LIB format"""
        # Check for basic elements
        required_elements = ["declare-", "assert", "=>"]
        if not all(element in smt_lib for element in required_elements):
            raise ValueError("SMT-LIB must contain declarations and assertions")
        
        # Check balanced parentheses
        if smt_lib.count('(') != smt_lib.count(')'):
            raise ValueError("Unbalanced parentheses in SMT-LIB expression")
        
        # Check for empty assertions
        if re.search(r'\(assert\s*\(\s*\)\s*\)', smt_lib):
            raise ValueError("Empty assertion in SMT-LIB")
        
        # Simple syntax check
        if not smt_lib.startswith("(") or not smt_lib.endswith(")"):
            raise ValueError("SMT-LIB must start and end with parentheses")
            
        # HTTP-specific validations
        if 'HTTPVersion' in smt_lib or 'Host' in smt_lib:
            # Check for required sorts
            required_sorts = ['Device', 'Request', 'Header', 'HeaderValue']
            for sort in required_sorts:
                if f'declare-sort {sort}' not in smt_lib:
                    raise ValueError(f"Missing required sort declaration: {sort}")
            
            # Check for required functions
            required_functions = [
                'HTTPVersion', 'HasHeader', 'HasHeaderValue',
                'ValidHeaderValue', 'CountHeaders'
            ]
            for func in required_functions:
                if f'declare-fun {func}' not in smt_lib and func in smt_lib:
                    raise ValueError(f"Function {func} used but not declared")
            
            # Check for host_header constant
            if 'host_header' in smt_lib and 'declare-const host_header Header' not in smt_lib:
                raise ValueError("Host header constant used but not declared")
            
    @staticmethod
    def available_models():
        """Return a list of recommended HuggingFace models for FOL conversion"""
        return [
            "mistralai/Mixtral-8x7B-Instruct-v0.1",  # Current default
            "meta-llama/Llama-2-70b-chat-hf",  # Large but powerful
            "google/gemma-7b-it",  # Good instruction following
            "NousResearch/Nous-Hermes-2-Mixtral-8x7B-DPO",  # Good for reasoning
            "01-ai/Yi-34B-Chat",  # Good performance on structured outputs
            "Anthropic/claude-3-sonnet-20240229",  # Very good at following instructions
        ]