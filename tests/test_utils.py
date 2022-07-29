import pytest
from atomkraft.utils import merge, query, update

merge_tests = [
    ({}, {1: 2}, {1: 2}),
    ({1: 2}, {1: 3}, {1: 3}),
    ({1: 3, 3: {2: 3}}, {3: {2: 4}}, {1: 3, 3: {2: 4}}),
]


@pytest.mark.parametrize("data, other, result", merge_tests)
def test_merge(data, other, result):
    assert merge(data, other) == result


query_tests = [
    ({"a": {"b": 2}}, None, {"a": {"b": 2}}),
    ({"a": {"b": 2}}, "", {"a": {"b": 2}}),
    ({"a": {"b": 2}}, "a", {"b": 2}),
    ({"a": {"b": 2}}, "a.b", 2),
]


@pytest.mark.parametrize("data, property_path, value", query_tests)
def test_query(data, property_path, value):
    assert query(data, property_path) == value


update_tests = [
    ({"a": {"b": 2}}, None, {"a": {"b": 3}}, {"a": {"b": 3}}),
    ({"a": {"b": 2}}, "", {"a": {"b": 3}}, {"a": {"b": 3}}),
    (
        {"a": {"b": 2}},
        "a",
        {"c": 3},
        {"a": {"b": 2, "c": 3}},
    ),
    ({"a": {"b": 2}}, "a.b", 4, {"a": {"b": 4}}),
]


@pytest.mark.parametrize("data, property_path, value, result", update_tests)
def test_update(data, property_path, value, result):
    assert update(data, property_path, value) == result
