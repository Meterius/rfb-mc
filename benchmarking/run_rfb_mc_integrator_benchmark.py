from fractions import Fraction
from typing import Tuple, List
from collections import Counter
from time import perf_counter
from benchmarking.benchmark import get_benchmark_list
from benchmarking.convert_benchmark_z3 import get_benchmark_formula
import os

from rfb_mc.component.eamp.eamp_edge_scheduler import EampEdgeScheduler
from rfb_mc.component.eamp.eamp_edge_scheduler_sp import EampEdgeSchedulerSP
from rfb_mc.component.eamp.eamp_rfmi_z3 import EampRfmiZ3
from rfb_mc.component.direct_integrator_z3 import DirectIntegratorZ3
from rfb_mc.component.runner_z3 import FormulaParamsZ3, RunnerZ3
from rfb_mc.component.in_memory_store import InMemoryStore
from rfb_mc.store import StoreData
from rfb_mc.types import Params


RunnerZ3.register_restrictive_formula_module_implementation(EampRfmiZ3)


def run_benchmark(benchmark: str) -> Tuple[float, Tuple[float, float]]:
    formula, variables = get_benchmark_formula(benchmark)

    print(f"Retrieved benchmark problem {benchmark}")

    store = InMemoryStore(
        data=StoreData(
            params=Params(
                bit_width_counter=Counter([x.size() for x in variables])
            )
        )
    )

    print("Setup Manager")

    scheduler = EampEdgeSchedulerSP(
        store=store,
        confidence=Fraction(0.95),
        a=100,
        q=2,
    )

    print("Setup Scheduler")

    integrator = DirectIntegratorZ3(
        formula_params=FormulaParamsZ3(
            formula=formula, variables=variables,
        ),
    )

    print("Setup Integrator")

    print("Integrator ------------------------")

    s1 = perf_counter()

    run = integrator.run(scheduler)

    try:
        while True:
            print(f"Intermediate Result: {next(run)}")
    except StopIteration as err:
        print(f"Result: {err.value}")
        return perf_counter() - s1, err.value


if __name__ == "__main__":
    c = 1

    tested_benchmarks: List[str] = ["case_1_b12_1", "squaring51"]

    code_dir = os.path.dirname(__file__)
    file_name = os.path.join(code_dir, "output", "benchmark_results.txt")

    # clear benchmark result files
    with open(file_name, "w") as fb:
        pass

    for benchmark in tested_benchmarks:
        print(f"Running Benchmark \"{benchmark}\"")
        for i in range(c):
            duration, result = run_benchmark(benchmark)

            # problem = get_benchmark_problem(benchmark)
            # s = perf_counter()
            # result = count_models_by_branching(problem.formula, problem.variables)
            # duration = perf_counter() - s
            # print(f"Running exact model count took {duration:.2f} seconds and returned {result}")

            with open(file_name, "a") as fb:
                fb.write(f"{benchmark};{i};{duration};{result}\n")

            # problem = get_benchmark_problem(benchmark)
            # s = perf_counter()
            # mc = count_models_by_branching(problem.formula, problem.variables)
            # d = perf_counter() - s
            # print(f"Running exact model count took {d:.2f} seconds and returned {mc}")
            #
            # with open(bc_file_name, "a") as fbc:
            #     fbc.write(f"{benchmark};{i};{c};{mc}\n")
