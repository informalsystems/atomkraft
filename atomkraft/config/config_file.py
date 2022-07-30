import tomlkit


class ConfigFile(object):
    def __init__(self, path: str):
        self.data = {}
        self.path = path

    def __enter__(self):
        self.fd = open(self.path, "w+")
        self.data = tomlkit.load(self.fd)
        return self

    def __exit__(self, type, value, traceback):
        self.fd.close()

    def get(self, key) -> str:
        if key in self.data:
            return self.data[key]
        if key.replace("-", "_") in self.data:
            return self.data[key.replace("-", "_")]
        if key.replace("_", "-") in self.data:
            return self.data[key.replace("_", "-")]
        raise KeyError

    def write(self, key, value):
        self.data[key] = value
        tomlkit.dump(self.data, self.fd)
