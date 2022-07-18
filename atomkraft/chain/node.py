import glob
import json
import os
import shutil
from dataclasses import dataclass
from subprocess import PIPE, Popen

import bip_utils
import hdwallet
import numpy as np
import toml
from hdwallet.symbols import ATOM


@dataclass
class ConfigPort:
    title: str
    config_file: str
    property_path: str


class Client:
    def __init__(self, home_dir, binary="gaiad"):
        self.home_dir = home_dir
        self.binary = binary


@dataclass
class Coin:
    denom: str
    amount: int
    expoent: int

    def __init__(self, amount, denom, exponent=6):
        self.amount = amount
        self.denom = denom
        self.expoent = exponent

    def __repr__(self):
        return f"{self.amount}{self.denom}"


class Account:
    def __init__(self, name, seed=None, strength=128):
        if strength not in [128, 160, 192, 224, 256]:
            raise ValueError(
                f"Strength should be one of the following [128, 160, 192, 224, 256], but it is not {strength}."
            )
        self.name = name
        if seed is None:
            seed = self.name
        self.entropy = (
            np.random.default_rng(list(seed.encode())).bytes(strength // 8).hex()
        )
        self.wallet = hdwallet.BIP44HDWallet(symbol=ATOM).from_entropy(
            entropy=self.entropy, language="english", passphrase=""
        )

    @property
    def mnemonic(self):
        return self.wallet.mnemonic()

    def address(self, prefix):
        return self.bech32_address(prefix)

    def validator_address(self, prefix):
        return self.bech32_address(f"{prefix}valoper")

    def bech32_address(self, prefix):
        return bip_utils.Bech32Encoder.Encode(prefix, bytes.fromhex(self.wallet.hash()))

    def __repr__(self):
        return json.dumps(self.wallet.dumps(), indent=2)


class Node:
    def __init__(
        self,
        moniker,
        chain_id,
        home_dir,
        *,
        overwrite=False,
        keep=False,
        binary="gaiad",
        denom="uatom",
        prefix="cosmos",
    ):
        self.moniker = moniker
        self.chain_id = chain_id
        self.home_dir = home_dir
        self.binary = binary
        self.denom = denom
        self.prefix = prefix
        self.overwrite = overwrite
        self.keep = keep
        self._popen = None
        self._stdout = None
        self._stderr = None

    def init(self):
        if self.overwrite:
            shutil.rmtree(self.home_dir)
        args = f"init {self.moniker} --chain-id {self.chain_id}".split()
        _, data = self._execute(args, stderr=PIPE)
        return json.loads(data.decode())

    def add_key(self, account: Account):
        argstr = (
            f"keys add {account.name} --recover --keyring-backend test --output json"
        )
        stdout, stderr = self._execute(
            argstr.split(),
            stdin=f"{account.wallet.mnemonic()}\n".encode(),
            stdout=PIPE,
            stderr=PIPE,
        )
        if stdout:
            return json.loads(stdout.decode())
        return json.loads(stderr.decode())

    def add_account(self, coin: Coin, account: Account):
        argstr = f"add-genesis-account {account.address(self.prefix)} {coin} --keyring-backend test --output json"
        self._execute(argstr.split())

    def add_validator(self, coin: Coin, account: Account):
        argstr = f"gentx {account.name} {coin} --keyring-backend test --chain-id {self.chain_id} --output json"
        self._execute(argstr.split(), stderr=PIPE)

    def collect_gentx(self):
        argstr = "collect-gentxs"
        _, data = self._execute(argstr.split(), stderr=PIPE)
        return json.loads(data.decode())

    def copy_gentx_from(self, other: "Node"):
        for file in glob.glob(f"{other.home_dir}/config/gentx/*.json"):
            shutil.copy(file, f"{self.home_dir}/config/gentx")

    def copy_genesis_from(self, other: "Node"):
        for file in glob.glob(f"{other.home_dir}/config/genesis.json"):
            shutil.copy(file, f"{self.home_dir}/config")

    def get(self, path, property_path=None):
        with open(f"{self.home_dir}/{path}", encoding="utf-8") as f:
            match os.path.splitext(path)[-1]:
                case ".json":
                    data = json.load(f)
                case ".toml":
                    data = toml.load(f)
                case _:
                    raise RuntimeError(f"Unexpected file {path}")
        if property_path is not None:
            keys = property_path.split(".")
            for key in keys:
                match data:
                    case dict():
                        try:
                            data = data[key]
                        except KeyError:
                            try:
                                data = data[key.replace("-", "_")]
                            except KeyError:
                                data = data[key.replace("_", "-")]
                            except Exception as e:
                                raise e
                    case list():
                        data = data[int(key)]
        return data

    def get_port(self, port_config: ConfigPort):
        return self.get(
            port_config.config_file,
            port_config.property_path,
        )

    def set(self, path, value, property_path=None):
        if property_path is not None:
            with open(f"{self.home_dir}/{path}", encoding="utf-8") as f:
                match os.path.splitext(path)[-1]:
                    case ".json":
                        main_data = json.load(f)
                    case ".toml":
                        main_data = toml.load(f)
                    case _:
                        raise RuntimeError(f"Unexpected file {path}")
            data = main_data
            keys = property_path.split(".")
            for key in keys[:-1]:
                match data:
                    case dict():
                        try:
                            data = data[key]
                        except KeyError:
                            try:
                                data = data[key.replace("-", "_")]
                            except KeyError:
                                data = data[key.replace("_", "-")]
                            except Exception as e:
                                raise e
                    case list():
                        data = data[int(key)]
            match data:
                case dict():
                    key = keys[-1]
                    try:
                        data[key] = value
                    except KeyError:
                        try:
                            data[key.replace("-", "_")] = value
                        except KeyError:
                            data[key.replace("_", "-")] = value
                        except Exception as e:
                            raise e
                case list():
                    data[int(keys[-1])] = value
        else:
            main_data = value
        with open(f"{self.home_dir}/{path}", "w", encoding="utf-8") as f:
            match os.path.splitext(path)[-1]:
                case ".json":
                    json.dump(main_data, f)
                case ".toml":
                    toml.dump(main_data, f)
                case _:
                    raise RuntimeError(f"Unexpected file {path}")

    def update(self, path, function, property_path=None):
        self.set(path, function(self.get(path, property_path)), property_path)

    def _execute(self, args, *, stdin: bytes | None = None, stdout=None, stderr=None):
        final_args = f"{self.binary} --home {self.home_dir}".split() + args
        # print(" ".join(final_args))
        stdin_pipe = None if stdin is None else PIPE
        with Popen(final_args, stdin=stdin_pipe, stdout=stdout, stderr=stderr) as p:
            out, err = p.communicate(input=stdin)
            rt = p.wait()
            if rt != 0:
                raise RuntimeError(f"Non-zero return code {rt}\n{err.decode()}")
            return (out, err)

    def __enter__(self):
        return self

    def sign(self, account, tx_file: str):
        argstr = f"tx sign {tx_file} --output-document {tx_file} --chain-id {self.chain_id} --overwrite --offline --sequence 0 --account-number 0 --from {account.name} --keyring-backend test --output json"
        self._execute(argstr.split())

    def start(self):
        self._stdout = open(f"{self.home_dir}/stdout.txt", "w", encoding="utf-8")
        self._stderr = open(f"{self.home_dir}/stderr.txt", "w", encoding="utf-8")
        args = f"{self.binary} start --home {self.home_dir}".split()
        self._popen = Popen(args, stdout=self._stdout, stderr=self._stderr)

    def close(self):
        if self._popen:
            self._popen.terminate()
            self._stdout.close()
            self._stderr.close()
            self._popen = None
            self._stdout = None
            self._stderr = None
        if not self.keep and os.path.isdir(self.home_dir):
            shutil.rmtree(self.home_dir)

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.close()

    def __del__(self):
        self.close()
