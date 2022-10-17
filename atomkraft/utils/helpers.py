# removes the suffix `suffix` from `text`.
# Implemented here as a helper fucntion in order to support Python 3.8
def remove_suffix(text: str, suffix: str):
    if text.endswith(suffix):
        text = text[: -len(suffix)]

    return text
