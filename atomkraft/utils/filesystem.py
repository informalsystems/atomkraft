import os
from pathlib import Path


def last_modified_file_in(dir: Path) -> str:
    """
    Return the path to the last modified file in `dir`.
    """
    all_files = Path(dir).glob(f"{dir}/*")
    return max(all_files, key=os.path.getctime)
