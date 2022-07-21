import ast
from typing import Set
from . import constants


class StepFunctionsVisitor(ast.NodeVisitor):
    def __init__(self) -> None:
        self.step_functions: Set[str] = set()
        super().__init__()

    def visit_FunctionDef(self, node: ast.FunctionDef) -> bool:
        print(f"visiting function {node.name}")

        for dec in node.decorator_list:
            if StepFunctionsVisitor._is_step(dec):
                self.step_functions.add(StepFunctionsVisitor.step_name(dec))

    @classmethod
    def _is_step(cls, dec):
        if isinstance(dec, ast.Call) and isinstance(dec.func, ast.Name):
            print(dec.func.id)
            if dec.func.id == "step":
                return True
        return False

    @classmethod
    def step_name(cls, dec):
        all_args = [a.value for a in dec.args]
        if len(all_args) == 0:
            return constants.ALL_ENCOMPASSING_STEP
        elif len(all_args) == 1:
            return all_args[0]
        else:
            raise ValueError("Step decorators except only a single argument")
