import pathlib
import re
from typing import List


def remove_prefix(text: str, prefix: str):
    """Removes the prefix `prefix` from `text`. Needed for Python 3.8."""
    if text.startswith(prefix):
        text = text[len(prefix) :]

    return text


def remove_suffix(text: str, suffix: str):
    """Removes the suffix `suffix` from `text`. Needed for Python 3.8."""
    if text.endswith(suffix):
        text = text[: -len(suffix)]

    return text


def natural_key(key: pathlib.Path) -> List[int]:
    """For sorting file paths containing numbers without leading zeroes"""
    return [int(s) if s.isdigit() else s.lower() for s in re.split("(\\d+)", str(key))]
