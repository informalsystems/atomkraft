from pathlib import Path
from typing import Any

import tomlkit


class ConfigFile(object):
    def __init__(self, path: Path):
        self.data = {}
        self.path = path

    def __enter__(self):
        self.fd = open(self.path, "a+")
        self.fd.seek(0)
        self.data = tomlkit.load(self.fd)
        return self

    def __exit__(self, type, value, traceback):
        self.fd.truncate(0)
        tomlkit.dump(self.data, self.fd)
        self.fd.close()

    def __getitem__(self, key) -> Any:
        return self.data[key]

    def __setitem__(self, key, value):
        self.data[key] = value

    def __delitem__(self, key):
        del self.data[key]

    def get_or_update(self, key: str, value: Any) -> Any:
        try:
            return self.data[key]
        except KeyError:
            self.data[key] = value
            return value

    def try_get(self, key: str, default: Any) -> Any:
        try:
            return self.data[key]
        except KeyError:
            return default
