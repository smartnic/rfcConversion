import spacy
from spacy.matcher import Matcher
from .llm import HFLLMConverter

class RFCToFOLConverter:
    def __init__(self):
        self.nlp = spacy.load("en_core_web_sm")
        self.matcher = Matcher(self.nlp.vocab)
        self._add_patterns()

    def _add_patterns(self):
        # Pattern for "IF X, MUST Y"
        pattern_if_must = [
            {"LOWER": "if"}, {"OP": "*"}, 
            {"LOWER": "must"}, {"OP": "*"}
        ]
        self.matcher.add("IF_MUST", [pattern_if_must])

    def parse_sentence(self, text):
        doc = self.nlp(text)
        matches = self.matcher(doc)
        
        if matches:
            # Simplified extraction (customize this!)
            condition = "received_SYN"
            subject = "Server"
            action = "send_SYN_ACK"
            return self._generate_fol(subject, condition, action)
        return None

    def _generate_fol(self, subject, condition, action):
        return f"∀x ({subject}(x) ∧ {condition}(x) → {action}(x))"

class HybridConverter:
    def __init__(self):
        self.rule_converter = RFCToFOLConverter()
        self.llm_converter = HFLLMConverter()

    def convert(self, text):
        rule_based_fol = self.rule_converter.parse_sentence(text)
        return rule_based_fol if rule_based_fol else self.llm_converter.extract_fol(text)