import sys
import py_compile

from atomkraft.reactor_room import reactor_room

# test if a correct reactor is generated for the arguments


# test if a generated reactor is syntactically correct
def test_parsing():
    actions_list = [["action_1", "action_2"], [], ["act"]]
    variables_list = [["a", "b", "c", "d"], [], ["a"]]
    for actions in actions_list:
        for variables in variables_list:
            reactor_stub_file = f"tests/project/reactors/reactor.py"
            reactor_room.generate_reactor(actions, variables, reactor_stub_file)
            compiled_reactor = py_compile.compile(reactor_stub_file)
            assert compiled_reactor is not None


# test if a reactor with not all actions implemented will be rejected


# test if a reactor which uses a wrong way to instantiate test functions will be rejected


#
