import shutil
from pathlib import Path
from typing import List, Union

import caseconverter


def last_modified_file_in(dir: Path) -> Path:
    """
    Return the path to the last modified file in `dir`.
    """
    all_files = Path(dir).glob(f"{dir}/*")
    return max(all_files, key=lambda x: x.stat().st_mtime)


def snakecase(path: str) -> str:
    return caseconverter.snakecase(path, delimiters="/.:-")


def copy_if_exists(srcs: Union[Path, List[Path]], dst_path: Path):
    if isinstance(srcs, Path):
        srcs = [srcs]
    dst_path.mkdir(parents=True, exist_ok=True)
    for src in srcs:
        if src.is_dir():
            shutil.copytree(src, dst_path / src.name)
        elif src.is_file():
            shutil.copy2(src, dst_path)
        else:
            # file does not exist
            pass
