import asyncio
import tempfile
import time
from contextlib import closing
from pathlib import Path
from typing import Dict, List, Optional, Union

import numpy as np
import tabulate
import tomlkit
from atomkraft.utils.project import ATOMKRAFT_INTERNAL_DIR, ATOMKRAFT_VAL_DIR_PREFIX
from grpclib.client import Channel
from terra_proto.cosmos.auth.v1beta1 import BaseAccount
from terra_proto.cosmos.auth.v1beta1 import QueryStub as AuthQueryStub
from terra_proto.cosmos.base.abci.v1beta1 import TxResponse
from terra_proto.cosmos.tx.v1beta1 import BroadcastMode, ServiceStub
from terra_sdk.client.lcd import LCDClient
from terra_sdk.client.lcd.api.tx import CreateTxOptions
from terra_sdk.core import Coins
from terra_sdk.core.fee import Fee
from terra_sdk.core.msg import Msg
from terra_sdk.key.mnemonic import MnemonicKey

from .node import Account, AccountId, ConfigPort, Node
from .utils import TmEventSubscribe, get_free_ports, update_port

VALIDATOR_DIR = "validator_nodes"

Bank = Dict[AccountId, Dict[str, int]]


class Testnet:
    def __init__(
        self,
        chain_id,
        validators: Union[int, List[AccountId]],
        accounts: Union[int, List[AccountId]],
        binary: Union[str, Path],
        denom: str,
        hrp_prefix: str,
        *,
        seed: Optional[str] = None,
        coin_type: int = 118,
        config_genesis: Dict = {},
        config_node: Dict = {},
        account_balance: Union[int, Bank] = 10**10,
        validator_balance: Union[int, Bank] = 10**10,
        overwrite: bool = True,
        keep: bool = True,
        verbose: bool = False,
        data_dir: Optional[Union[str, Path]] = None,
    ):
        self.chain_id: str = chain_id
        self.set_accounts(accounts)
        self.set_validators(validators)
        self._account_seed = seed
        self.binary: Path = Path(binary) if isinstance(binary, str) else binary
        self.denom = denom
        self.hrp_prefix: str = hrp_prefix

        self.coin_type: int = coin_type
        self.config_genesis: Dict = config_genesis
        self.config_node: Dict = config_node
        if isinstance(account_balance, int):
            account_balance_d = dict()
            for e in self._account_ids:
                account_balance_d[e] = dict()
                account_balance_d[e][self.denom] = account_balance
            account_balance = account_balance_d
        self.set_account_balances(account_balance)
        if isinstance(validator_balance, int):
            validator_balance_d = dict()
            for e in self._validator_ids:
                validator_balance_d[e] = dict()
                validator_balance_d[e][self.denom] = validator_balance
            validator_balance = validator_balance_d
        self.set_validator_balances(validator_balance)
        self.overwrite: bool = overwrite
        self.keep = keep
        self.verbose = verbose
        if data_dir is None:
            data_dir = Path(ATOMKRAFT_INTERNAL_DIR)
        elif isinstance(data_dir, str):
            data_dir = Path(data_dir)
        self.data_dir = data_dir / VALIDATOR_DIR

    def set_account_balances(self, balances: Bank):
        self.account_balances = balances

    def set_validator_balances(self, balances: Bank):
        self.validator_balances = balances

    def set_accounts(self, accounts: Union[int, List[AccountId]]):
        if isinstance(accounts, list):
            self._account_ids = accounts
        elif isinstance(accounts, int):
            self._account_ids = list(range(accounts))
        else:
            self._account_ids = list(accounts)

    def set_validators(self, validators: Union[int, List[AccountId]]):
        if isinstance(validators, list):
            self._validator_ids = validators
        elif isinstance(validators, int):
            self._validator_ids = list(range(validators))
        else:
            self._validator_ids = list(validators)
        self._lead_validator = self._validator_ids[0]

    def acc_addr(self, id: AccountId) -> str:
        if id not in self.accounts:
            self.accounts[id] = Account(
                id, group="acc", seed=self._account_seed, coin_type=self.coin_type
            )
        return self.accounts[id].address(self.hrp_prefix)

    def val_addr(self, id: AccountId, valoper: bool = False) -> str:
        if id not in self.validators:
            self.validators[id] = Account(
                id, group="val", seed=self._account_seed, coin_type=self.coin_type
            )
        if valoper:
            return self.validators[id].validator_address(self.hrp_prefix)
        else:
            return self.validators[id].address(self.hrp_prefix)

    def finalize_accounts(self):
        self.validators: Dict[AccountId, Account] = {
            v: Account(
                v, group="val", seed=self._account_seed, coin_type=self.coin_type
            )
            for v in self._validator_ids
        }
        self.accounts: Dict[AccountId, Account] = {
            a: Account(
                a, group="acc", seed=self._account_seed, coin_type=self.coin_type
            )
            for a in self._account_ids
        }

    @staticmethod
    def load_toml(path: Path, **kwargs):
        with open(path) as f:
            data = tomlkit.load(f)

        for (k, v) in kwargs.items():
            data[k] = str(v)

        return Testnet(**data)

    @staticmethod
    def ports() -> Dict[str, ConfigPort]:
        data = {}

        # config.toml
        data["p2p"] = ConfigPort("P2P", Path("config/config.toml"), "p2p.laddr")
        # data["p2p_ext"] = ConfigPort("P2P External", "config/config.toml", "p2p.external_address")
        data["abci"] = ConfigPort("ABCI", Path("config/config.toml"), "proxy_app")
        data["pprof_laddr"] = ConfigPort(
            "PPROF", Path("config/config.toml"), "rpc.pprof_laddr"
        )
        data["rpc"] = ConfigPort("RPC", Path("config/config.toml"), "rpc.laddr")
        data["prometheus"] = ConfigPort(
            "Prometheus",
            Path("config/config.toml"),
            "instrumentation.prometheus_listen_addr",
        )

        # app.toml
        data["lcd"] = ConfigPort("LCD", Path("config/app.toml"), "api.address")
        data["grpc"] = ConfigPort("gRPC", Path("config/app.toml"), "grpc.address")
        data["grpc-web"] = ConfigPort(
            "gRPC", Path("config/app.toml"), "grpc-web.address"
        )
        # dict["rosetta"] = ConfigPort("Rosetta", "config/app.toml", "rosetta.address")
        return data

    def get_validator_port(self, validator_id: AccountId, port_type: str):
        return self.validator_nodes[validator_id].get_port(self.ports()[port_type])

    def get_grpc_channel(self, validator_id: Optional[AccountId] = None) -> Channel:
        if validator_id is None:
            validator_id = self._lead_validator
        grpc_ip, grpc_port = self.get_validator_port(validator_id, "grpc").split(":", 1)
        return Channel(host=grpc_ip, port=int(grpc_port))

    def prepare(self):
        self.finalize_accounts()
        self.data_dir.mkdir(parents=True, exist_ok=True)
        self.data_dir = Path(
            tempfile.mkdtemp(prefix=ATOMKRAFT_VAL_DIR_PREFIX, dir=str(self.data_dir))
        )
        self.validator_nodes = {
            validator_id: Node(
                f"node_{validator_id}",
                self.chain_id,
                self.data_dir / f"node_{validator_id}",
                overwrite=self.overwrite,
                keep=self.keep,
                binary=Path(self.binary),
                denom=self.denom,
                hrp_prefix=self.hrp_prefix,
            )
            for validator_id in self.validators.keys()
        }

        for node in self.validator_nodes.values():
            node.init()

        for (k, v) in self.config_genesis.items():
            self.validator_nodes[self._lead_validator].set(
                Path("config/genesis.json"), v, k
            )

        for (v_id, validator) in self.validators.items():
            self.validator_nodes[self._lead_validator].add_account(
                validator, self.validator_balances[v_id]
            )

        for (a_id, account) in self.accounts.items():
            self.validator_nodes[self._lead_validator].add_account(
                account, self.account_balances[a_id]
            )

        for node_id, node in self.validator_nodes.items():
            if node_id != self._lead_validator:
                self.validator_nodes[node_id].copy_genesis_from(
                    self.validator_nodes[self._lead_validator]
                )

        # very hacky
        all_ports = (
            np.array(get_free_ports(len(self.ports()) * (len(self.validators) - 1)))
            .reshape((-1, len(self.ports())))
            .tolist()
        )

        all_port_data = []

        for (node_id, node) in self.validator_nodes.items():
            for (config_file, configs) in self.config_node.items():
                for (k, v) in configs.items():
                    if isinstance(v, str):
                        # TODO: avoid tomlkit.items.str being a list
                        node.set(Path(f"config/{config_file}.toml"), str(v), k)
                    else:
                        node.set(Path(f"config/{config_file}.toml"), v, k)

            if node_id != self._lead_validator:
                ports = all_ports.pop()
                for (j, e_port) in enumerate(self.ports().values()):
                    node.update(
                        e_port.config_file,
                        lambda x: update_port(x, ports[j]),
                        e_port.property_path,
                    )

            port_data = [node.moniker]
            for e_port in self.ports().values():
                port_data.append(node.get(e_port.config_file, e_port.property_path))
            all_port_data.append(port_data)

        if self.verbose:
            print(
                tabulate.tabulate(
                    all_port_data,
                    headers=["Moniker"] + [e.title for e in self.ports().values()],
                )
            )

            print(
                tabulate.tabulate(
                    [
                        [validator.address(self.hrp_prefix)]
                        for validator in self.validators.values()
                    ],
                    headers=["Validators"],
                )
            )

            print(
                tabulate.tabulate(
                    [
                        [account.address(self.hrp_prefix)]
                        for account in self.accounts.values()
                    ],
                    headers=["Accounts"],
                )
            )

        for (node_id, node) in self.validator_nodes.items():
            node.add_key(self.validators[node_id])
            p2p = self.ports()["p2p"]
            node.add_validator(
                self.validators[node_id], self.validator_balances[node_id][self.denom]
            )

            if node_id != self._lead_validator:
                # because this
                # https://github.com/cosmos/cosmos-sdk/blob/88ee7fb2e9303f43c52bd32410901841cad491fb/x/staking/client/cli/tx.go#L599
                gentx_file = next(node.home_dir.glob("config/gentx/*json"))
                gentx_file = gentx_file.relative_to(node.home_dir)
                node_p2p = node.get(p2p.config_file, p2p.property_path).rsplit(
                    ":", maxsplit=1
                )[-1]
                node.update(gentx_file, lambda x: update_port(x, node_p2p), "body.memo")
                node.sign(self.validators[node_id], node.home_dir / gentx_file)

        for (id_a, node_a) in self.validator_nodes.items():
            for (id_b, node_b) in self.validator_nodes.items():
                if id_a != id_b:
                    node_a.copy_gentx_from(node_b)

        for node in self.validator_nodes.values():
            node.collect_gentx()

    def spinup(self):
        for node in self.validator_nodes.values():
            node.start()
        endpoint_types = ["rpc", "grpc"]
        for node in self.validator_nodes.values():
            for endpoint_type in endpoint_types:
                node.wait_for_port(self.ports()[endpoint_type])
        print("Endpoints are ready:", " ".join(endpoint_types))

    def oneshot(self):
        self.prepare()
        self.spinup()

    def teardown(self):
        for node in self.validator_nodes.values():
            node.close()

    def broadcast_transaction(
        self,
        account_id: AccountId,
        msgs: Union[Msg, List[Msg]],
        *,
        gas: int = 200_000,
        fee_amount: int = 0,
        validator_id: Optional[AccountId] = None,
    ) -> TxResponse:
        if validator_id is None:
            validator_id = self._lead_validator

        if not isinstance(msgs, list):
            msgs = [msgs]

        account = self.accounts[account_id]

        lcdclient = LCDClient("ip", chain_id="phoenix-1")
        lcdclient.chain_id = self.chain_id

        if account.mnemonic is None:
            raise ValueError(f"Account({account.name}) do not have mnemonic")

        wallet = lcdclient.wallet(
            MnemonicKey(
                mnemonic=account.mnemonic,
                coin_type=self.coin_type,
            )
        )

        with closing(self.get_grpc_channel(validator_id=validator_id)) as channel:
            stub = AuthQueryStub(channel)
            result = asyncio.run(stub.account(address=account.address(self.hrp_prefix)))
            account_info = BaseAccount().parse(result.account.value)
            account_number = account_info.account_number
            sequence = account_info.sequence

            tx = wallet.create_and_sign_tx(
                CreateTxOptions(
                    msgs,
                    fee=Fee(gas, Coins(f"{fee_amount}{self.denom}")),
                    account_number=account_number,
                    sequence=sequence,
                )
            )

            service = ServiceStub(channel)

            with TmEventSubscribe({"tm.event": "Tx"}) as subscriber:
                # # BROADCAST_MODE_SYNC defines a tx broadcasting mode where the client waits
                # # for a CheckTx execution response only.
                # BROADCAST_MODE_SYNC = 2
                result = asyncio.run(
                    service.broadcast_tx(
                        tx_bytes=bytes(tx.to_proto()),
                        mode=BroadcastMode.BROADCAST_MODE_SYNC,
                    )
                ).tx_response
                if result.code == 0:
                    # CheckTx execution was successful, check for block execution result
                    subscriber.set_filter(
                        lambda x: x["events"]["tx.hash"][0] == result.txhash
                    )

            # wait a little for data availablity
            # may vary on different computers
            # TODO: remove this sleep and use some event based technique
            time.sleep(0.1)

            # # following works, but waits till next block, so waits longer
            # with TmEventSubscribe({"tm.event": "NewBlock"}):
            #     pass

            if result.code == 0:
                result = asyncio.run(service.get_tx(hash=result.txhash)).tx_response

        return result
