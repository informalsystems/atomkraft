import ast
from typing import Set
from . import constants


class StepFunctionsVisitor(ast.NodeVisitor):
    """
    This visitor will upon visiting a function definition explore if this function is decorated
    by @step (in method visit_FunctionDef). All other nodes will be simply traversed.
    """

    def __init__(self) -> None:
        self.step_functions: Set[str] = set()
        super().__init__()

    def visit_FunctionDef(self, node: ast.FunctionDef) -> bool:
        for dec in node.decorator_list:
            if StepFunctionsVisitor._is_step(dec):
                self.step_functions.add(StepFunctionsVisitor.step_name(dec))

    @classmethod
    def _is_step(cls, dec) -> bool:

        # only accepts decorators of the form @step(...)
        if isinstance(dec, ast.Call):
            if dec.func.id == "step":
                return True
        return False

    @classmethod
    def step_name(cls, dec):
        # get all the arguments of the decorator `dec`
        all_args = [a.value for a in dec.args]

        if len(all_args) == 0:
            # if it comes with no arguments, this is a decorator that can be applied to any action
            return constants.ALL_ENCOMPASSING_STEP
        elif len(all_args) == 1:
            return all_args[0]
        else:
            # step decorators should never receive more than one argument. Raising exception if that happens
            raise ValueError(
                "Step decorators accept only one argument: a name of the step to be matched by the decorated function"
            )
