import pytest
from src.specifications.tcp_specification import TCPSpecification

@pytest.fixture
def tcp_spec():
    return TCPSpecification()

def test_tcp_nodes(tcp_spec):
    """Test that TCP specification has correct node types"""
    assert 'TCPEndpoint' in tcp_spec.node_types
    assert 'Initiator' in tcp_spec.node_types
    assert 'Responder' in tcp_spec.node_types

def test_tcp_states(tcp_spec):
    """Test that TCP specification has correct states"""
    assert 'CLOSED' in tcp_spec.states
    assert 'LISTEN' in tcp_spec.states
    assert 'ESTABLISHED' in tcp_spec.states
    assert 'SYN_SENT' in tcp_spec.states
    assert 'SYN_RECEIVED' in tcp_spec.states

def test_tcp_predicates(tcp_spec):
    """Test that TCP specification has correct predicate categories"""
    predicates = tcp_spec.get_all_predicates()
    assert 'node_predicates' in predicates
    assert 'message_predicates' in predicates
    assert 'action_predicates' in predicates
    assert 'state_predicates' in predicates
    assert 'relation_predicates' in predicates

def test_state_transitions(tcp_spec):
    """Test that TCP specification has correct state transitions"""
    transitions = tcp_spec.get_state_transitions('CLOSED')
    assert 'LISTEN' in transitions
    assert 'SYN_SENT' in transitions

def test_predicate_validation(tcp_spec):
    """Test predicate validation"""
    assert tcp_spec.validate_predicate('hasSequenceNumber', 'message_predicates')
    assert not tcp_spec.validate_predicate('invalid_predicate', 'message_predicates') 