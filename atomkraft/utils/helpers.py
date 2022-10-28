import re


# removes the suffix `suffix` from `text`.
# Implemented here as a helper fucntion in order to support Python 3.8
def remove_suffix(text: str, suffix: str):
    if text.endswith(suffix):
        text = text[: -len(suffix)]

    return text


def natural_sort(key):
    """For sorting strings containing numbers without leading zeroes"""
    return [int(s) if s.isdigit() else s.lower() for s in re.split("(\\d+)", str(key))]
