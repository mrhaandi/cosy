from itertools import islice
import time
from collections.abc import Callable, Iterable
from typing import Any

from cosy.core.solution_space import (
    Argument,
    SolutionSpace,
)
from cosy.core.synthesizer import C
from cosy.core.types import Group, Type

from cosy.core.solution_space import (
    NonTerminalArgument,
)

from cosy.core.solution_space import (
    NonTerminalArgument,
)


def binary_non_terminal_tree(*, bound: int = 50000):
    def construct_rules():
        yield (
            "Root",
            "root",
            (
                NonTerminalArgument(name=None, origin="Tree1"),
                NonTerminalArgument(name=None, origin="Tree2"),
            ),
            (),
        )
        total_non_terminals_created = 1
        for nodes in range(1, bound // 2):
            yield (
                f"Tree{nodes}",
                f"tree{nodes}",
                (
                    NonTerminalArgument(name=None, origin=f"Tree{nodes*2 + 1}"),
                    NonTerminalArgument(name=None, origin=f"Tree{nodes*2 + 2}"),
                ),
                (),
            )
            total_non_terminals_created += 1
        for leaves in range(bound // 2, bound):
            yield (
                f"Tree{leaves}",
                f"tree{leaves}_l",
                (),
                (),
            )
            yield (
                f"Tree{leaves}",
                f"tree{leaves}_r",
                (),
                (),
            )
            total_non_terminals_created += 1
        assert total_non_terminals_created == bound, "bound was not reached"

    target = "Root"

    return target, construct_rules()


def binary_terminal_tree(*, bound: int = 500):
    def construct_rules():
        yield (
            "Root",
            "root_l",
            (NonTerminalArgument(name=None, origin="Tree1"),),
            (),
        )
        yield (
            "Root",
            "root_r",
            (NonTerminalArgument(name=None, origin="Tree2"),),
            (),
        )

        total_non_terminals_created = 1

        for i in range(1, bound // 2):
            yield (
                f"Tree{i}",
                f"tree{i}_l",
                (NonTerminalArgument(name=None, origin=f"Tree{i*2 + 1}"),),
                (),
            )
            yield (
                f"Tree{i}",
                f"tree{i}_r",
                (NonTerminalArgument(name=None, origin=f"Tree{i*2 + 2}"),),
                (),
            )

            total_non_terminals_created += 1

        for leaves in range(bound // 2, bound):
            yield (f"Tree{leaves}", f"tree{leaves}_l", (), ())
            yield (f"Tree{leaves}", f"tree{leaves}_r", (), ())
            total_non_terminals_created += 1

        assert total_non_terminals_created == bound, "bound was not reached"

    target = "Root"
    return target, construct_rules()


def w_d_tree(*, w: int = 10, d: int = 10):
    def construct_rules():
        for i in range(0, d):
            yield (
                f"Node{i}",
                f"node{i}",
                (
                    # generator to create *w* nodes
                    tuple(NonTerminalArgument(None, f"Node{i+1}") for j in range(w))
                ),
                (),
            )

        yield (
            f"Node{d}",
            f"left_node{d}",
            (),
            (),
        )

        yield (
            f"Node{d}",
            f"right_node{d}",
            (),
            (),
        )

    target = "Node0"

    return target, construct_rules()


def d_binary_w_facts_tree(*, w: int = 10, d: int = 10):
    def construct_rules():
        for i in range(0, d):
            yield (
                f"Node{i}",
                f"node{i}",
                (tuple(NonTerminalArgument(None, f"Node{i+1}") for _ in range(2))),
                (),
            )

        for j in range(0, w):
            yield (
                f"Node{d}",
                f"node{d}_{j}",
                (),
                (),
            )

    target = "Node0"

    return target, construct_rules()


def goal_stratification(*, w: int = 10):
    def construct_rules():
        yield (
            "Tree0",
            "tree0",
            (NonTerminalArgument("Tree1", "Tree1"),),
            (),
        )

        yield (
            "Tree1",
            "tree1",
            tuple(NonTerminalArgument(None, "Tree2") for _ in range(w)),
            (),
        )

        yield (
            "Tree2",
            "tree2",
            (NonTerminalArgument(None, "Tree3"),),
            (),
        )

        yield (
            "Tree3",
            "tree3",
            tuple(NonTerminalArgument(None, "Tree4") for _ in range(w)),
            (),
        )

        yield (
            "Tree4",
            "tree4_l",
            (),
            (),
        )

        yield (
            "Tree4",
            "tree4_r",
            (),
            (),
        )

    target = "Tree0"

    return target, construct_rules()


def goal_stratification_modified_no_stratification(*, w: int = 10):
    def construct_rules():
        yield (
            "Tree1",
            "tree1",
            tuple(NonTerminalArgument(None, "Tree2") for _ in range(w)),
            (),
        )

        yield (
            "Tree2",
            "tree2",
            (NonTerminalArgument(None, "Tree3"),),
            tuple(NonTerminalArgument(None, "Tree3") for _ in range(w)),
            (),
        )

        yield (
            "Tree3",
            "tree3",
            tuple(NonTerminalArgument(None, "Tree4") for _ in range(w)),
            (),
        )

        yield (
            "Tree4",
            "tree4_l",
            (),
            (),
        )

        yield (
            "Tree4",
            "tree4_r",
            (),
            (),
        )

    target = "Tree1"

    return target, construct_rules()


def goal_stratification_modified_no_middle(*, w: int = 10):
    def construct_rules():
        yield (
            "Tree0",
            "tree0",
            (NonTerminalArgument(None, "Tree1"),),
            (),
        )

        yield (
            "Tree1",
            "tree1",
            tuple(NonTerminalArgument(None, "Tree3") for _ in range(w)),
            (),
        )

        yield (
            "Tree3",
            "tree3",
            tuple(NonTerminalArgument(None, "Tree4") for _ in range(w)),
            (),
        )

        yield (
            "Tree4",
            "tree4_l",
            (),
            (),
        )

        yield (
            "Tree4",
            "tree4_r",
            (),
            (),
        )

    target = "Tree0"

    return target, construct_rules()


def goal_stratification_modified_no_stratification_middle(*, w: int = 10):
    def construct_rules():
        yield (
            "Tree1",
            "tree1",
            tuple(NonTerminalArgument(None, "Tree3") for _ in range(w)),
            (),
        )

        yield (
            "Tree3",
            "tree3",
            tuple(NonTerminalArgument(None, "Tree4") for _ in range(w)),
            (),
        )

        yield (
            "Tree4",
            "tree4_l",
            (),
            (),
        )

        yield (
            "Tree4",
            "tree4_r",
            (),
            (),
        )

    target = "Tree1"

    return target, construct_rules()


def chain_graph(*, bound: int = 53000):
    def construct_rules():
        yield ("Node1", "base", (), ())

        total_non_terminals_created = 1

        for i in range(2, bound + 1):
            yield (
                f"Node{i}",
                f"step{i}_{i-1}",
                (NonTerminalArgument(name=None, origin=f"Node{i - 1}"),),
                (),
            )
            total_non_terminals_created += 1

        assert total_non_terminals_created == bound, "bound was not reached"

    target_type = "Node" + str(bound)

    return (target_type, construct_rules())


def chain_graph_with_predicates(*, bound: int = 53000):
    def construct_rules():
        yield (
            "Node1",
            "base",
            (),
            (lambda _: True,),
        )
        total_non_terminals_created = 1
        for i in range(2, bound + 1):
            yield (
                f"Node{i}",
                f"step{i}_{i - 1}",
                (NonTerminalArgument(name=None, origin=f"Node{i - 1}"),),
                (lambda _: True,),
            )
            total_non_terminals_created += 1
        assert total_non_terminals_created == bound, "bound was not reached"

    target_type = "Node" + str(bound)
    return target_type, construct_rules()


def benchmark(
    *,
    css: tuple[
        Any,
        Iterable[
            tuple[
                Any,
                Any,
                tuple[Argument, ...],
                tuple[Callable[[dict[str, Any]], bool], ...],
            ]
        ],
    ],
    name: str,
    max_count: int | None = None,
) -> None:
    solution_space: SolutionSpace[Type, C, Group] = SolutionSpace()
    for cs in css[1]:
        solution_space.add_rule(*cs)
    trees = solution_space.enumerate_trees(start=css[0])

    if max_count is not None:
        trees = islice(trees, max_count)
        suffix = f" with max count {max_count}"
    else:
        suffix = ""

    tree_count = 0
    print(f"| {name} {suffix} | ", end="")
    start_time = time.time()
    for tree in trees:
        tree_count += 1
    end_time = time.time()
    print(f"{end_time - start_time} seconds |")


def benchmark_incremental(
    *,
    css: tuple[
        Any,
        Iterable[
            tuple[
                Any,
                Any,
                tuple[Argument, ...],
                tuple[Callable[[dict[str, Any]], bool], ...],
            ]
        ],
    ],
    name: str,
    max_count: int | None = None,
) -> None:
    solution_space: SolutionSpace[Type, C, Group] = SolutionSpace()
    for cs in css[1]:
        solution_space.add_rule(*cs)
    trees = solution_space.enumerate_trees_lazy(start=css[0])

    if max_count is not None:
        trees = islice(trees, max_count)
        suffix = f" with max count {max_count}"
    else:
        suffix = ""

    print(f"{name} {suffix}")
    tree_count = 0
    start_total_time = time.time()
    start_time = time.time()
    for tree in trees:
        end_time = time.time()
        tree_count += 1
        print(f"enumerate another tree {tree_count}: {end_time - start_time} seconds")
        start_time = time.time()
    print(f"total runtime: {end_time - start_total_time} seconds")
    print(f"total tree: {tree_count}")

from cosy.core.solution_space import (
    NonTerminalArgument,
)


def directed_k_cyclic_graph(*, bound: int = 50000):
    def construct_rules():
        # create target node
        yield (
            "Target",
            "target",
            (NonTerminalArgument("intoCycle", f"Step{bound - 2}"),),
            (),
        )

        # create base node
        yield (
            "Base",
            "base",
            (),
            (),
        )

        total_non_terminals_created = 2

        # crate a k-cyclic graph
        for i in range(1, bound - 1):
            if i == (bound // 2):
                yield (
                    f"Step{i}",
                    f"step_{i}",
                    (
                        NonTerminalArgument(
                            name=f"nextVertex{(i % (bound - 2)) + 1}",
                            origin=f"Step{(i % (bound - 2)) + 1}",
                        ),
                        NonTerminalArgument(name="exit", origin="Base"),
                    ),
                    (),
                )
                # This second role has to be added so the solution can branch off to the base rule as exit
                # if this rule is not added there is no rule that can be added due to cyclic dependency
                yield (
                    f"Step{i}",
                    f"step_{i}_base",
                    (NonTerminalArgument(name="exit", origin="Base"),),
                    (),
                )
            else:
                yield (
                    f"Step{i}",
                    f"step_{i}",
                    (
                        NonTerminalArgument(
                            f"nextVertex{(i % (bound - 2)) + 1}",
                            f"Step{(i % (bound - 2)) + 1}",
                        ),
                    ),
                    (),
                )
            total_non_terminals_created += 1

        assert total_non_terminals_created == bound, "bound was not reached"

    target = "Target"

    return target, construct_rules()

benchmark_incremental(css=directed_k_cyclic_graph(), name="first test", max_count=100)
