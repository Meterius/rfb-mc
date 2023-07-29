import os
from typing import Iterable


def resolve(*path: Iterable[str]) -> str:
    code_dir = os.path.dirname(__file__)
    return os.path.join(code_dir, *path)


def get_benchmark_list():
    return list(sorted(os.listdir(resolve("benchmarks"))))


def get_benchmark_smt2(benchmark: str) -> str:
    smt2_file_dir = resolve("benchmarks", benchmark)
    smt2_file = resolve("benchmarks", benchmark, os.listdir(smt2_file_dir)[0])

    with open(smt2_file, "r") as f:
        return f.read()
