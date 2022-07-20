from os import PathLike
from typing import List


def generate_reactor(
    actions_list: List[str], variables_list: List[str], stub_file_path: PathLike = None
) -> PathLike:

    print("Generating something :)")
    print(actions_list, variables_list, stub_file_path)
