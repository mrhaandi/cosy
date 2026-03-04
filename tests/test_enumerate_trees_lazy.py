# regression test for contains_tree
from collections.abc import Callable
import itertools

import pytest

from cosy.core.solution_space import NonTerminalArgument, SolutionSpace
from cosy.core.specification_builder import SpecificationBuilder
from cosy.core.synthesizer import Synthesizer
from cosy.core.tree import Tree
from cosy.core.types import DataGroup, Literal, Var


T = int | Callable

def test_contains_tree_simple() -> None:
    solution_space = SolutionSpace()
    solution_space.add_rule("Tree0", "t0", (NonTerminalArgument(None, "Tree1"),), ())
    solution_space.add_rule("Tree0", "t0_rec", (NonTerminalArgument(None, "Tree0"),), ())
    solution_space.add_rule("Tree1", "t1_l", (), ())
    solution_space.add_rule("Tree1", "t1_r", (), ())

    for tree in itertools.islice(solution_space.enumerate_trees_lazy("Tree0"), 10):
        print(tree)

def test_contains_tree() -> None:
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

test_contains_tree()
