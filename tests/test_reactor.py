import sys
import py_compile

from atomkraft.reactor import reactor

# test if a correct reactor is generated for the arguments


# test if a generated reactor is syntactically correct
def test_parsing():
    actions_list = [["action_1", "action_2"], [], ["act"]]
    variables_list = [["a", "b", "c", "d"], [], ["a"]]
    for actions in actions_list:
        for variables in variables_list:
            reactor_stub_file = f"tests/project/reactors/reactor.py"
            reactor.generate_reactor(
                actions, variables, stub_file_path=reactor_stub_file
            )
            compiled_reactor = py_compile.compile(reactor_stub_file)
            assert compiled_reactor is not None


def test_check():
    actions = ["store_cw_contract", "instantiate", "get_count", "increment", "reset"]
    variables = ["owner", "instantiated", "stepCount", "messages", "count", "last_msg"]
    reactor_stub_file = f"tests/project/reactors/check_correct_reactor.py"
    generated_reactor = reactor.generate_reactor(
        actions, variables, stub_file_path=reactor_stub_file, keypath="last_msg.name"
    )
    reactor_ok = reactor.check_reactor(
        trace="tests/project/traces/sample_trace.itf.json", reactor=generated_reactor
    )
    assert reactor_ok is True

    # test that the reactor with missing actions will be deemed incorrect
    reactor_stub_file = f"tests/project/reactors/check_faulty_reactor.py"
    modified_actions = actions[:2]
    generated_reactor = reactor.generate_reactor(
        modified_actions,
        variables,
        stub_file_path=reactor_stub_file,
        keypath="last_msg.name",
    )
    reactor_ok = reactor.check_reactor(
        trace="tests/project/traces/sample_trace.itf.json", reactor=generated_reactor
    )
    assert reactor_ok is False

    # tets that the reactor which contains an all-encompassing actios is deemed correct
    reactor_ok = reactor.check_reactor(
        trace="tests/project/traces/sample_trace.itf.json",
        reactor="tests/project/reactors/sample_reactor.py",
    )
    assert reactor_ok is True
