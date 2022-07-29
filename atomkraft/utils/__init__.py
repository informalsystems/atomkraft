import copy
from typing import Any, Dict


def query(
    data: Dict[Any, Any],
    property_path: str | None,
) -> Any:
    if property_path:
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


def merge(old: Any, new: Any):
    if isinstance(old, Dict):
        old = copy.deepcopy(old)
        for (key, val) in new.items():
            if key in old and isinstance(val, dict):
                old[key] = merge(old[key], val)
            else:
                old[key] = val
        return old
    else:
        return new


def update(data_root: Dict[Any, Any], property_path: str | None, value: Any) -> Any:
    if property_path:
        data = data_root
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
                case list():
                    data = data[int(key)]
        match data:
            case dict():
                key = keys[-1]
                try:
                    data[key] = merge(data[key], value)
                except KeyError:
                    try:
                        cust_key = key.replace("-", "_")
                        data[cust_key] = merge(data[cust_key], value)
                    except KeyError:
                        cust_key = key.replace("_", "-")
                        data[cust_key] = merge(data[cust_key], value)
            case list():
                cust_key = int(keys[-1])
                data[cust_key] = merge(data[cust_key], value)
    else:
        data_root = merge(data_root, value)
    return data_root
