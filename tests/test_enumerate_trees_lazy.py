# regression test for contains_tree
from collections.abc import Callable
import itertools

import pytest

from cosy.core.solution_space import ConstantArgument, NonTerminalArgument, SolutionSpace
from cosy.core.specification_builder import SpecificationBuilder
from cosy.core.synthesizer import Synthesizer
from cosy.core.tree import Tree
from cosy.core.types import DataGroup, Literal, Var


T = int | Callable

def test_enumerate_trees_lazy_simple() -> None:
    solution_space = SolutionSpace()
    solution_space.add_rule("Tree0", "t0", (NonTerminalArgument(None, "Tree1"),), ())
    solution_space.add_rule("Tree0", "t0_rec", (NonTerminalArgument(None, "Tree0"),), ())
    solution_space.add_rule("Tree1", "t1_l", (), ())
    solution_space.add_rule("Tree1", "t1_r", (), ())

    for tree in itertools.islice(solution_space.enumerate_trees_lazy("Tree0"), 10):
        print(tree)

def test_enumerate_trees_lazy() -> None:
    solution_space = SolutionSpace()
    width = 20
    solution_space.add_rule("Tree0", "t0", (NonTerminalArgument(None, "Tree1"),), ())
    solution_space.add_rule("Tree1", "t1", tuple(NonTerminalArgument(None, "Tree2") for _ in range(width)), ())
    solution_space.add_rule("Tree2", "t2", (NonTerminalArgument(None, "Tree3"),), ())
    solution_space.add_rule("Tree3", "t3", tuple(NonTerminalArgument(None, "Tree4") for _ in range(width)), ())
    solution_space.add_rule("Tree4", "t4_l", (), ())
    solution_space.add_rule("Tree4", "t4_r", (), ())

    for tree in itertools.islice(solution_space.enumerate_trees_lazy("Tree0"), 100):
    #for tree in itertools.islice(solution_space.enumerate_trees("Tree0", 10), 100):
        print(tree)

def test_enumerate_trees_lazy_complex() -> None:
    solution_space = SolutionSpace()
    arguments = (ConstantArgument("x", 0, None),
                NonTerminalArgument("v", "T1"),
                ConstantArgument("y", 1, None),
                NonTerminalArgument("w", "T1"),
                NonTerminalArgument(None, "T1"),
                ConstantArgument("z", 2, None),
                NonTerminalArgument(None, "T1"))
    predicates = (lambda vs: vs["v"] == vs["w"],
                  lambda vs: vs["x"] == 0 and vs["y"] == 1 and vs["z"] == 2,)
    solution_space.add_rule("T0", "t", arguments, predicates)
    solution_space.add_rule("T1", "l", (), ())
    solution_space.add_rule("T1", "r", (), ())

    trees = set()
    exptected_results = {
        "t 0 l 1 l l 2 l",
        "t 0 r 1 r r 2 r",
        "t 0 r 1 r r 2 l",
        "t 0 r 1 r l 2 r",
        "t 0 r 1 r l 2 l",
        "t 0 l 1 l r 2 r",
        "t 0 l 1 l r 2 l",
        "t 0 l 1 l l 2 r"
    }

    for tree in itertools.islice(solution_space.enumerate_trees_lazy("T0"), 100):
        trees.add(str(tree))
        print(tree)

    assert trees == exptected_results

test_enumerate_trees_lazy_complex()
