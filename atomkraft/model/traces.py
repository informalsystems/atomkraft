from pathlib import Path
from typing import List

from atomkraft.config.atomkraft_config import AtomkraftConfig
from atomkraft.config.model_config import ModelConfig
from atomkraft.utils.filesystem import last_modified_file_in
from modelator.cli.model_config_file import load_config_file
from modelator.itf import ITF
from modelator.Model import Model
from modelator.ModelResult import ModelResult


def query_configs(key: str) -> str:
    with AtomkraftConfig() as atomkraft_config:
        with ModelConfig() as model_config:
            try:
                return model_config.query(key) or atomkraft_config.query(key)
            except KeyError:
                raise FileNotFoundError


def generate_traces(
    model_config_path=None, model_path=None, sample_operators=[]
) -> ModelResult:
    """
    Call Modelator to get samples of the given model in `model_path`. Return the
    result of running the checker as a ModelResult.

    If a `model_config_path` is provided, use that to load the model path.
    Otherwise, use `model_path` and `sample_operators`.

    Raise an exception when a required parameter is absent, or when they are not
    available via defaults, or when the parameters are invalid.
    """
    init = "Init"
    next = "Next"
    if model_config_path:
        model_config = load_config_file(model_config_path)
        model_path = model_config["model_path"]
        init = model_config["init"] or init
        next = model_config["next"] or next
        sample_operators = list(set(model_config["examples"] + sample_operators))

    if not model_path:
        raise ValueError("No model path given.")

    if not Path(model_path).is_file():
        raise FileNotFoundError(f"File with model not found: {model_path}")

    model = Model.parse_file(model_path, init, next)
    return model.sample(examples=sample_operators)


def last_modified_trace_path() -> str:
    """
    Return the path to the last modified trace file in the trace directory.
    """
    try:
        traces_dir = query_configs("traces_dir")
    except FileNotFoundError:
        raise FileNotFoundError(
            "No trace directory set in neither model or configuration file."
        )

    if not Path(traces_dir).is_dir():
        raise FileNotFoundError(f"Directory does not exist: {traces_dir}")

    return last_modified_file_in(traces_dir)


def get_trace(trace_path=None) -> List["ITF"]:
    """
    Return a trace represented as an ITF class from Modelator. If `trace_path`
    is absent, return the last trace generated with the `model` command.
    """
    if not trace_path:
        trace_path = last_modified_trace_path()

    if not Path(trace_path).is_file():
        raise FileNotFoundError(f"Path {trace_path} is not a file")

    print(f"Retrieving trace from: {trace_path}")
    return ITF.from_itf_json(trace_path)
