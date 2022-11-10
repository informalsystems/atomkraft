import asyncio
import json
import socket
from typing import Any, Callable, Dict, List, Optional

import websockets
from jsonrpcclient import responses
from jsonrpcclient.requests import request_json


def get_free_ports(n: int) -> List[int]:
    """Get free ports from OS

    Args:
        n (int): Requested number of ports

    Returns:
        List[int]: List of free port
    """
    socks = []
    ports = []
    for _ in range(n):
        sock = socket.socket()
        sock.bind(("", 0))
        ports.append(sock.getsockname()[1])
        socks.append(sock)
    for sock in socks:
        sock.close()
    return ports


def update_port(old: str, new: int) -> str:
    """Replace port in `old` with `new`

    `update_port("localhost:123", "321") = "localhost:321"`

    Args:
        old (str): Old IP with port
        new (int): New port

    Returns:
        str: New IP with port
    """
    old_port = old.split(":")[-1]
    return old.replace(old_port, str(new))


class TmEventSubscribe:
    def __init__(
        self, params: Dict[str, str], filter: Optional[Callable[[Any], bool]] = None
    ):
        """Create Tendermint event subscriber.

        `with TmEventSubscribe({"tm.event": "NewBlock"}) as subscriber:`
        will exit only after a new block is generated.

        Args:
            params (Dict[str, str]): Event parsms
            filter (Optional[Callable[[Any], bool]], optional): Filter on events. Defaults to None.
        """
        self.params: Dict[str, str] = params
        self.filter: Optional[Callable[[Any], bool]] = filter

    def set_filter(self, func: Callable[[Any], bool]):
        """Set event filter later.

        Args:
            func (Callable[[Any], bool]): Filter on tendermint events
        """
        self.filter = func

    async def _subscribe(self):
        self.websocket = await websockets.connect("ws://0.0.0.0:26657/websocket")
        self.query = " AND ".join(
            f"{key} = '{value}'" for (key, value) in self.params.items()
        )
        req = request_json("subscribe", params={"query": self.query})
        await self.websocket.send(req)

    def __enter__(self):
        self.loop = asyncio.new_event_loop()
        self.loop.run_until_complete(self._subscribe())
        return self

    async def _wait(self):
        # if no transaction is created inside `with TmEventSubscribe(...)`,
        # tx event polling will be stuck. the following early-return avoids it.
        # note: it can still get stuck if it subscribes for an event that will not
        # be produced by the blockchain.
        # Eg. `Tx` event with an incorrect transaction filter
        if self.params.get("tm.event", None) == "Tx" and self.filter is None:
            return
        while True:
            msg = responses.to_result(json.loads(await self.websocket.recv()))
            if (
                isinstance(msg, responses.Ok)
                and msg.result.get("query", None) == self.query
                and (self.filter is None or self.filter(msg.result))
            ):
                break

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.loop.run_until_complete(self._wait())
        self.loop.run_until_complete(self.websocket.close())
        self.loop.close()
