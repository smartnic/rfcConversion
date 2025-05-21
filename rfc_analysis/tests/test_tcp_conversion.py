import unittest
from src.tcp_specification import TCPSpecification
from examples.tcp_examples import TCPExample

class TestTCPConversion(unittest.TestCase):
    def setUp(self):
        self.tcp_spec = TCPSpecification()
        self.examples = TCPExample.get_examples()
    
    def test_predicate_categories(self):
        """Test if all predicate categories are properly defined"""
        categories = self.tcp_spec.get_predicate_categories()
        self.assertIn('node', categories)
        self.assertIn('message', categories)
        self.assertIn('action', categories)
        self.assertIn('state', categories)
        self.assertIn('relation', categories)
    
    def test_tcp_states(self):
        """Test if TCP states are properly defined"""
        states = self.tcp_spec.states
        self.assertIn('CLOSED', states)
        self.assertIn('LISTEN', states)
        self.assertIn('SYN_SENT', states)
        self.assertIn('SYN_RECEIVED', states)
        self.assertIn('ESTABLISHED', states)
    
    def test_example_conversions(self):
        """Test example RFC statements and their FOL representations"""
        for example in self.examples:
            # Verify that the requirement is not empty
            self.assertTrue(example['requirement'])
            # Verify that the FOL representation is not empty
            self.assertTrue(example['fol'])
            # Verify that the explanation is not empty
            self.assertTrue(example['explanation'])
    
    def test_state_transitions(self):
        """Test TCP state transitions"""
        transitions = TCPExample.get_state_transitions()
        for from_state, to_state, description in transitions:
            # Verify that the transition is valid according to the specification
            self.assertIn(to_state, self.tcp_spec.get_state_transitions(from_state))
    
    def test_message_sequences(self):
        """Test TCP message sequences"""
        sequences = TCPExample.get_message_sequences()
        for sequence in sequences:
            # Verify that the sequence name is not empty
            self.assertTrue(sequence['name'])
            # Verify that the sequence steps are not empty
            self.assertTrue(sequence['sequence'])
            # Verify that the FOL representation is not empty
            self.assertTrue(sequence['fol'])

if __name__ == '__main__':
    unittest.main() 