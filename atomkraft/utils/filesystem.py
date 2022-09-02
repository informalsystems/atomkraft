from pathlib import Path


def last_modified_file_in(dir: Path) -> Path:
    """
    Return the path to the last modified file in `dir`.
    """
    all_files = Path(dir).glob(f"{dir}/*")
    return max(all_files, key=lambda x: x.stat().st_mtime)
