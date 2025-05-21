import unittest
from unittest.mock import patch
from src.llm import HFLLMConverter

class TestHFLLMConverter(unittest.TestCase):
    @patch('huggingface_hub.InferenceClient.text_generation')
    def test_extract_fol(self, mock_text_gen):
        mock_text_gen.return_value = "FOL: ∀p (Packet(p) → valid(p))"
        converter = HFLLMConverter()
        self.assertEqual(converter.extract_fol("test"), "∀p (Packet(p) → valid(p))")