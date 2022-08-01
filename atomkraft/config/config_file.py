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

    def query(self, key) -> str:
        if key not in self.data:
            raise KeyError
        return self.data[key]

    def store(self, key, value):
        self.data[key] = value
        tomlkit.dump(self.data, self.fd)
