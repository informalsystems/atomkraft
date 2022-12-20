import logging
import time
from atomkraft.chain import Testnet
from atomkraft.chain.testnet import Testnet
from atomkraft.utils.project import ATOMKRAFT_INTERNAL_DIR, ATOMKRAFT_VAL_DIR_PREFIX
from modelator.pytest.decorators import step
from terra_sdk.core.bank.msgs import MsgSend
import json


@step("Init")
def init(testnet: Testnet, action, balances):
    root_logger = logging.getLogger()
    root_logger.setLevel(logging.DEBUG)

    handler = logging.FileHandler("debug_log.txt")
    handler.setLevel(logging.DEBUG)
    formatter = logging.Formatter("%(asctime)s.%(msecs)03d;%(levelname)s;%(message)s",
                                  "%Y-%m-%d %H:%M:%S")
    handler.setFormatter(formatter)
    root_logger.addHandler(handler)

    logging.info("Step: Init")
    testnet.set_accounts(action.value.wallets)
    testnet.set_account_balances(balances)
    testnet.verbose = True
    testnet.oneshot()
    logging.info("Status: Testnet launched\n")


@step("Transfer")
def transfer(testnet: Testnet, action):
    startTime = time.time()
    action = action.value

    sender_id = action.sender
    receiver_id = action.receiver
    amount = action.amount

    sender_addr = testnet.acc_addr(sender_id)
    receiver_addr = testnet.acc_addr(receiver_id)

    # important that this is imported from terra_sdk, not terra_proto.cosmos
    msg = MsgSend(sender_addr, receiver_addr, f"{amount}{testnet.denom}")

    logging.info("Sending transfer")
    logging.info(f"\tSender:    {sender_id} ({sender_addr})")
    logging.info(f"\tReceiver:  {receiver_id} ({receiver_addr})")
    logging.info(f"\tAmount:    {msg.amount}")

    result = testnet.sign_and_broadcast(
        sender_id, msg, gas=200_000, fee_amount=0)

    if result:
        result = json.loads(result)

    if not result or result["code"] != 0:
        logging.info("Status: Error")
        logging.info(f"\tcode: {result['code']}")
        logging.info(f"\tlog:  {result['raw_log']}\n")
    else:
        logging.info("Status: Successful\n")

    logging.debug(f"[MSG] {msg}")
    logging.debug(f"[RES] {result}")

    endTime = time.time()
    logging.info(f"Took {endTime - startTime}s to send transfer")

    with open("new_times.txt", 'a') as file:
        file.write(f"{endTime - startTime}\n")
