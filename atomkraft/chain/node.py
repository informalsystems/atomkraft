import glob
import json
import os
import shutil
import socket
from dataclasses import dataclass
from pathlib import Path
from subprocess import PIPE, Popen
from typing import Any, Callable, Dict, List, Optional, Tuple, Union

import bip_utils
import hdwallet
import numpy as np
import tenacity
import tomlkit
from hdwallet.cryptocurrencies import CoinType, Cryptocurrency

from .. import utils


@dataclass
class ConfigPort:
    title: str
    config_file: Path
    property_path: str


class Client:
    def __init__(self, home_dir: Path, binary: Path):
        self.home_dir = home_dir
        self.binary = binary


@dataclass
class Coin:
    denom: str
    amount: int
    expoent: int

    def __init__(self, amount: int, denom: str, exponent: int = 6):
        self.amount = amount
        self.denom = denom
        self.expoent = exponent

    def __repr__(self) -> str:
        return f"{self.amount}{self.denom}"


AccountId = Union[int, str]


class Account:
    def __init__(
        self,
        name: AccountId,
        group: Optional[str] = None,
        seed: Optional[str] = None,
        strength: int = 128,
        coin_type: int = 118,
    ):
        if strength not in [128, 160, 192, 224, 256]:
            raise ValueError(
                f"Strength should be one of the following [128, 160, 192, 224, 256], but it is not {strength}."
            )
        self.name = name
        final_seed = Path(str(self.name))
        if group:
            final_seed /= group
        if seed:
            final_seed /= str(seed)
        self.entropy = (
            np.random.default_rng(list(bytes(final_seed))).bytes(strength // 8).hex()
        )
        self.coin_type = coin_type

        class LocalCC(Cryptocurrency):
            COIN_TYPE = CoinType({"INDEX": self.coin_type, "HARDENED": True})

        self.wallet = hdwallet.BIP44HDWallet(cryptocurrency=LocalCC).from_entropy(
            entropy=self.entropy, language="english", passphrase=""
        )

    @property
    def mnemonic(self) -> Optional[str]:
        return self.wallet.mnemonic()

    def address(self, prefix) -> str:
        return self.bech32_address(prefix)

    def validator_address(self, prefix) -> str:
        return self.bech32_address(f"{prefix}valoper")

    def bech32_address(self, prefix) -> str:
        return bip_utils.Bech32Encoder.Encode(prefix, bytes.fromhex(self.wallet.hash()))

    def __repr__(self) -> str:
        return json.dumps(self.wallet.dumps(), indent=2)


class Node:
    def __init__(
        self,
        moniker: str,
        chain_id: str,
        home_dir: Path,
        binary: Path,
        *,
        overwrite: bool = False,
        keep: bool = False,
        denom: str = "uatom",
        hrp_prefix: str = "cosmos",
    ):
        self.moniker = moniker
        self.chain_id = chain_id
        self.home_dir = home_dir
        self.binary = binary
        self.denom = denom
        self.hrp_prefix = hrp_prefix
        self.overwrite = overwrite
        self.keep = keep
        self._popen = None
        self._stdout = None
        self._stderr = None

    def init(self) -> Optional[Dict]:
        if self.overwrite and os.path.exists(self.home_dir):
            shutil.rmtree(self.home_dir)
        argstr = f"init {self.moniker} --chain-id {self.chain_id}"
        return self._json_from_stdout_or_stderr(*self._execute(argstr.split()))

    def add_key(self, account: Account) -> Optional[Dict]:
        argstr = (
            f"keys add {account.name} --recover --keyring-backend test --output json"
        )
        return self._json_from_stdout_or_stderr(
            *self._execute(
                argstr.split(),
                stdin=f"{account.wallet.mnemonic()}\n".encode(),
            )
        )

    def add_account(self, account: Account, coins: Union[Dict[str, int], int]):
        if isinstance(coins, int):
            coins = {self.denom: coins}
        coins_str = ",".join(f"{amount}{denom}" for (denom, amount) in coins.items())
        argstr = f"add-genesis-account {account.address(self.hrp_prefix)} {coins_str} --keyring-backend test --output json"
        self._execute(argstr.split())

    def add_validator(self, account: Account, staking_amount: int):
        argstr = f"gentx {account.name} {staking_amount}{self.denom} --keyring-backend test --chain-id {self.chain_id} --output json"
        self._execute(argstr.split(), stderr=PIPE)

    def collect_gentx(self):
        argstr = "collect-gentxs"
        return self._json_from_stdout_or_stderr(*self._execute(argstr.split()))

    def copy_gentx_from(self, other: "Node"):
        for file in glob.glob(f"{other.home_dir}/config/gentx/*.json"):
            shutil.copy(file, f"{self.home_dir}/config/gentx")

    def copy_genesis_from(self, other: "Node"):
        for file in glob.glob(f"{other.home_dir}/config/genesis.json"):
            shutil.copy(file, f"{self.home_dir}/config")

    def get(self, path: Path, property_path: Optional[str] = None):
        with open(self.home_dir / path, encoding="utf-8") as f:
            if path.suffixes[-1] == ".json":
                data = json.load(f)
            elif path.suffixes[-1] == ".toml":
                data = tomlkit.load(f)
            else:
                raise RuntimeError(f"Unexpected file {path}")
        return utils.query(data, property_path)

    def get_port(self, port_config: ConfigPort):
        return self.get(
            port_config.config_file,
            port_config.property_path,
        )

    @tenacity.retry(
        retry=tenacity.retry_if_exception_type((ConnectionRefusedError)),
        wait=tenacity.wait_fixed(0.3),
        stop=tenacity.stop_after_delay(600),
    )
    def wait_for_port(self, port_config: ConfigPort):
        addr = self.get(
            port_config.config_file,
            port_config.property_path,
        )
        ip, port = addr.split("//")[-1].split(":")
        with socket.create_connection(
            (ip, port),
            timeout=5,
        ):
            pass

    def set(self, path: Path, value: Any, property_path: Optional[str] = None):
        if property_path is not None:
            with open(self.home_dir / path, encoding="utf-8") as f:
                if os.path.splitext(path)[-1] == ".json":
                    main_data = json.load(f)
                elif os.path.splitext(path)[-1] == ".toml":
                    main_data = tomlkit.load(f)
                else:
                    raise RuntimeError(f"Unexpected file {path}")
            main_data = utils.update(main_data, property_path, value)
        else:
            main_data = value
        with open(self.home_dir / path, "w", encoding="utf-8") as f:
            if os.path.splitext(path)[-1] == ".json":
                json.dump(main_data, f)
            elif os.path.splitext(path)[-1] == ".toml":
                tomlkit.dump(main_data, f)
            else:
                raise RuntimeError(f"Unexpected file {path}")

    def update(
        self,
        path: Path,
        function: Callable[[Any], Any],
        property_path: Optional[str] = None,
    ):
        self.set(path, function(self.get(path, property_path)), property_path)

    def _execute(
        self,
        args: List[str],
        *,
        stdin: Optional[bytes] = None,
        stdout: Optional[int] = None,
        stderr: Optional[int] = None,
    ) -> Tuple[Optional[bytes], Optional[bytes]]:
        final_args = f"{self.binary} --home {self.home_dir}".split() + args
        # print(" ".join(final_args))
        stdin_pipe = None if stdin is None else PIPE
        with Popen(final_args, stdin=stdin_pipe, stdout=stdout, stderr=stderr) as p:
            out, err = p.communicate(input=stdin)
            rt = p.wait()
            if rt != 0:
                raise RuntimeError(f"Non-zero return code {rt}\n{err.decode()}")
            return (out, err)

    def _json_from_stdout_or_stderr(
        self,
        stdout: Optional[bytes],
        stderr: Optional[bytes],
    ) -> Optional[Dict]:
        if stdout and stdout.strip() and stderr and stderr.strip():
            raise RuntimeWarning(
                f"Got non-empty output on stdout and stderr:\n\n{stdout.decode()}\n\n{stderr.decode()}"
            )

        if stdout and stdout.strip():
            try:
                return json.loads(stdout.decode())
            except json.decoder.JSONDecodeError:
                pass

        if stderr and stderr.strip():
            try:
                return json.loads(stderr.decode())
            except json.decoder.JSONDecodeError:
                return

    def __enter__(self):
        return self

    def sign(self, account: Account, tx_file: Path):
        argstr = f"tx sign {tx_file} --output-document {tx_file} --chain-id {self.chain_id} --overwrite --offline --sequence 0 --account-number 0 --from {account.name} --keyring-backend test --output json"
        self._execute(argstr.split())

    def start(self):
        self._stdout = open(self.home_dir / "stdout.txt", "w", encoding="utf-8")
        self._stderr = open(self.home_dir / "stderr.txt", "w", encoding="utf-8")
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
