import unittest
from src.converter import RFCToFOLConverter, HybridConverter

class TestRuleBasedConverter(unittest.TestCase):
    def setUp(self):
        self.converter = RFCToFOLConverter()

    def test_if_must_rule(self):
        sentence = "If a SYN is received, the server MUST send a SYN-ACK."
        expected = "∀x (Server(x) ∧ received_SYN(x) → send_SYN_ACK(x))"
        self.assertEqual(self.converter.parse_sentence(sentence), expected)

class TestHybridConverter(unittest.TestCase):
    def setUp(self):
        self.converter = HybridConverter()

    def test_hybrid_fallback(self):
        sentence = "Clients MUST NOT reuse ports under any circumstances."
        # Assuming rule-based can't parse this
        self.assertTrue("¬reuse" in self.converter.convert(sentence))