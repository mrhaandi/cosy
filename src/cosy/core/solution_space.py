"""Solution space given by a logic program."""

from __future__ import annotations

from collections import defaultdict, deque
from collections.abc import Callable, Hashable, Iterable, Mapping, Sequence
from dataclasses import dataclass
from itertools import product
from types import FunctionType
from typing import Any, Generic, TypeVar

from cosy.core.tree import Tree

NT = TypeVar("NT", bound=Hashable)  # type of non-terminals
T = TypeVar("T", bound=Hashable)  # type of terminals
G = TypeVar("G", bound=Hashable)  # type of constants


@dataclass(frozen=True)
class ConstantArgument(Generic[T, G]):
    name: str
    value: T
    origin: G


@dataclass(frozen=True)
class NonTerminalArgument(Generic[NT]):
    name: str | None
    origin: NT


Argument = ConstantArgument[T, G] | NonTerminalArgument[NT]


@dataclass(frozen=True)
class RHSRule(Generic[NT, T, G]):
    arguments: tuple[Argument, ...]
    predicates: tuple[Callable[[dict[str, Any]], bool], ...]
    terminal: T

    @property
    def non_terminals(self) -> frozenset[NT]:
        """Set of non-terminals occurring in the body of the rule."""
        return frozenset(arg.origin for arg in self.arguments if isinstance(arg, NonTerminalArgument))

    @property
    def literal_substitution(self):
        return {n.name: n.value for n in self.arguments if isinstance(n, ConstantArgument)}

import heapq

class AgingPriorityQueue(Generic[NT]):
    # (effective_priority, tiebreaker, item)
    _heap: list[tuple[int, int, NT]]
    _clock: int
    _index: int
    _items: set[NT]

    def __init__(self):
        self._heap = []
        self._clock = 0
        self._index = 0
        self._items = set()

    def contains(self, item: NT) -> bool:
        return item in self._items

    def empty(self) -> bool:
        return not self._heap

    def enqueue(self, item: NT, priority: int) -> None:
        if item not in self._items:
            heapq.heappush(self._heap, (priority + self._clock, self._index, item))
            self._index += 1
            self._items.add(item)

    def dequeue(self) -> NT:
        self._clock += 1
        _, _, item = heapq.heappop(self._heap)
        self._items.remove(item)
        return item

class SolutionSpace(Generic[NT, T, G]):
    _rules: defaultdict[NT, deque[RHSRule[NT, T, G]]]
    _occurrences: dict[NT, deque[tuple[NT, RHSRule[NT, T, G]]]]

    def __init__(self) -> None:
        self._rules = defaultdict(deque)
        self._occurrences = defaultdict(deque)

    def get(self, nonterminal: NT) -> deque[RHSRule[NT, T, G]] | None:
        return self._rules.get(nonterminal)

    def __getitem__(self, nonterminal: NT) -> deque[RHSRule[NT, T, G]]:
        return self._rules[nonterminal]

    def nonterminals(self) -> Iterable[NT]:
        return self._rules.keys()

    def as_tuples(self) -> Iterable[tuple[NT, deque[RHSRule[NT, T, G]]]]:
        return self._rules.items()

    def add_rule(
        self,
        nonterminal: NT,
        terminal: T,
        arguments: tuple[Argument, ...],
        predicates: tuple[Callable[[dict[str, Any]], bool], ...],
    ) -> None:
        # add the rule to the solution space and add occurrences of non-terminals in the rule
        rule = RHSRule(arguments, predicates, terminal)
        self._rules[nonterminal].append(rule)
        for m in rule.non_terminals:
            self._occurrences[m].append((nonterminal, rule))

    def show(self) -> str:
        return "\n".join(
            f"{nt!s} ~> {' | '.join([str(subrule) for subrule in rule])}" for nt, rule in self._rules.items()
        )

    def prune(self) -> SolutionSpace[NT, T, G]:
        """Keep only productive rules."""

        ground_types: set[NT] = set()
        queue: set[NT] = set()
        inverse_grammar: dict[NT, set[tuple[NT, frozenset[NT]]]] = defaultdict(set)

        for n, exprs in self._rules.items():
            for expr in exprs:
                non_terminals = expr.non_terminals
                for m in non_terminals:
                    inverse_grammar[m].add((n, non_terminals))
                if not non_terminals:
                    queue.add(n)

        while queue:
            n = queue.pop()
            if n not in ground_types:
                ground_types.add(n)
                for m, non_terminals in inverse_grammar[n]:
                    if m not in ground_types and all(t in ground_types for t in non_terminals):
                        queue.add(m)

        result: SolutionSpace[NT, T, G] = SolutionSpace[NT, T, G]()
        for target in ground_types:
            for possibility in self._rules[target]:
                if all(t in ground_types for t in possibility.non_terminals):
                    result.add_rule(target, possibility.terminal, possibility.arguments, possibility.predicates)
        return result

    def _enumerate_tree_vectors_lazy(
        self,
        non_terminals: Sequence[NT | None],
        existing_trees: list[list[Tree[T] | None]],
        nt_term: tuple[NT, Tree[T]] | None = None,
    ) -> Iterable[tuple[Tree[T] | None, ...]]:
        """Enumerate possible tree vectors for a given list of non-terminals and existing trees. Use nt_term at least once (if given)."""
        if nt_term is None:
            yield from product(*([n] if n is None else trees for n, trees in zip(non_terminals, existing_trees, strict=True)))
        else:
            nt, term = nt_term
            for i, n in enumerate(non_terminals):
                if n == nt:
                    arg_lists: Iterable[Iterable[Tree[T] | None]] = (
                        [None] if m is None else [term] if i == j else trees
                        for j, (m, trees) in enumerate(zip(non_terminals, existing_trees, strict=True))
                    )
                    yield from product(*arg_lists)

    def _generate_new_trees_lazy(
        self,
        rule: RHSRule[NT, T, G],
        existing_trees: list[list[Tree[T] | None]],
        interpretation: dict[T, Any] | None = None,
        nt_old_term: tuple[NT, Tree[T]] | None = None,
    ) -> Iterable[Tree[T]]:
        # Iterate over new trees for rule `rule` from existing trees
        # the term `old_term` should be a subterm of all resulting terms, at a position, that corresponds to `nt`

        named_non_terminals = [
            a.origin if isinstance(a, NonTerminalArgument) and a.name is not None else None for a in rule.arguments
        ]
        unnamed_non_terminals = [
            a.origin if isinstance(a, NonTerminalArgument) and a.name is None else None for a in rule.arguments
        ]
        literal_arguments = [Tree(a.value, ()) if isinstance(a, ConstantArgument) else None for a in rule.arguments]

        def interleave(
            parameters: Sequence[Tree[T] | None],
            arguments: Sequence[Tree[T] | None],
        ) -> Iterable[Tree[T]]:
            """Interleave parameters, literal arguments and arguments."""
            return (next(tree for tree in candidates if tree is not None) for candidates in zip(parameters, literal_arguments, arguments, strict=True))

        def valid_parameters(
            nt_term: tuple[NT, Tree[T]] | None,
        ) -> Iterable[tuple[Tree[T] | None, ...]]:
            """Enumerate all valid parameters for the rule."""
            for parameters in self._enumerate_tree_vectors_lazy(named_non_terminals, existing_trees, nt_term):
                if rule.predicates:
                    # compute the specific substitution only if there are predicates
                    substitution = {
                        a.name: p if interpretation is None else p.interpret(interpretation)
                        for p, a in zip(parameters, rule.arguments, strict=True)
                        if isinstance(a, NonTerminalArgument) and a.name is not None and p is not None
                    } | rule.literal_substitution
                    if all(predicate(substitution) for predicate in rule.predicates):
                        yield parameters
                else:
                    yield parameters

        # nt_old_term occurs in parameters
        for parameters in valid_parameters(nt_old_term):
            for arguments in self._enumerate_tree_vectors_lazy(unnamed_non_terminals, existing_trees):
                yield Tree(rule.terminal, tuple(interleave(parameters, arguments)))

        # nt_old_term occurs in arguments
        if nt_old_term is not None:
            all_parameters: deque[tuple[Tree[T] | None, ...]] | None = None
            for arguments in self._enumerate_tree_vectors_lazy(unnamed_non_terminals, existing_trees, nt_old_term):
                all_parameters = all_parameters if all_parameters is not None else deque(valid_parameters(None))
                for parameters in all_parameters:
                    yield Tree(rule.terminal, tuple(interleave(parameters, arguments)))

        return

    def enumerate_trees_lazy(
        self,
        start: NT,
        interpretation: dict[T, Any] | None = None,
    ) -> Iterable[Tree[T]]:
        """
        Enumerate trees as a lazy iterator efficiently - all terms are enumerated, no guaranteed term order.
        """
        if start not in self.nonterminals():
            return

        # 1. Compute distances from `start` through the grammar
        # distances[n] is the minimum number of rule-applications on the path from start to n
        # start has distance 0; unreachable non-terminals have distance -1
        distances: dict[NT, int] = {n: -1 for n in self.nonterminals()}
        distances[start] = 0
        # shorter paths are prioritized by this factor
        factor: int = 10
        pending_distances: deque[NT] = deque([start])
        while pending_distances:
            n = pending_distances.popleft()
            d = distances[n]
            for rule in self._rules[n]:
                for m in rule.non_terminals:
                    if distances[m] == -1 or distances[m] > d + factor:
                        distances[m] = d + factor
                        pending_distances.append(m)

        # trees discovered but not yet incorporated
        pending_trees: dict[NT, deque[Iterable[Tree[T]]]] = {n: deque() for n in self.nonterminals()}
        # trees already incorporated
        existing_trees: dict[NT, set[Tree[T]]] = {n: set() for n in self.nonterminals()}
        # non-terminals with pending trees:smaller distance means higher priority, aging prevents starvation
        queue: AgingPriorityQueue[NT] = AgingPriorityQueue()

        # 2. Generate reachable trees with no arguments
        for n, exprs in self._rules.items():
            for expr in exprs:
                if not expr.non_terminals:
                    pending_trees[n].append(self._generate_new_trees_lazy(expr, [[] for _ in expr.arguments]))
                    if distances[n] >= 0:
                        queue.enqueue(n, distances[n])

        # 3. Process one pending tree per iteration
        while not queue.empty():
            n = queue.dequeue()
            tree: Tree[T] | None = None

            while pending_trees[n] and tree is None:
                tree = next(pending_trees[n][0], None)
                if tree is None:
                    pending_trees[n].popleft()

            if tree is not None:
                # re-enqueue n because more trees might still be pending
                queue.enqueue(n, distances[n])
                if tree not in existing_trees[n]:
                    existing_trees[n].add(tree)
                    # yield immediately if this is a tree for the start non-terminal
                    if n == start:
                        yield tree
                    for m, expr in self._occurrences[n]:
                        queue.enqueue(m, distances[m])
                        # current trees for the non-terminals in the rule, used to generate new trees for m
                        current_trees: list[list[Tree[T] | None]] = [list(existing_trees[argument.origin]) if isinstance(argument, NonTerminalArgument) else [None] for argument in expr.arguments]
                        pending_trees[m].append(self._generate_new_trees_lazy(expr, current_trees, interpretation, (n, tree)))

        return

    def contains_tree(self, start: NT, tree: Tree[T], interpretation: dict[T, Any] | None = None) -> bool:
        """Check if the solution space contains a given `tree` derivable from `start`."""
        if start not in self.nonterminals():
            return False

        stack: deque[tuple | Callable] = deque([(start, tree)])
        results: deque[bool] = deque()

        def get_inputs(count: int) -> list[bool]:
            return [results.pop() for _ in range(count)]

        while stack:
            task = stack.pop()
            if isinstance(task, tuple):
                nt, tree = task
                relevant_rhss = [
                    rhs
                    for rhs in self._rules[nt]
                    if len(rhs.arguments) == len(tree.children)
                    and rhs.terminal == tree.root
                    and all(
                        argument.value == child.root and len(child.children) == 0
                        for argument, child in zip(rhs.arguments, tree.children, strict=True)
                        if isinstance(argument, ConstantArgument)
                    )
                ]

                # disjunction of the results for individual rules
                def or_inputs(count: int = len(relevant_rhss)) -> None:
                    results.append(any(get_inputs(count)))

                stack.append(or_inputs)

                for rhs in relevant_rhss:
                    substitution = {
                        argument.name: child.root
                        if isinstance(argument, ConstantArgument)
                        else (child if interpretation is None else child.interpret(interpretation))
                        for argument, child in zip(rhs.arguments, tree.children, strict=True)
                        if argument.name is not None
                    }

                    # conjunction of the results for individual arguments in the rule
                    def and_inputs(
                        count: int = sum(1 for argument in rhs.arguments if isinstance(argument, NonTerminalArgument)),
                        substitution: dict[str, Any] = substitution,
                        predicates=rhs.predicates,
                    ) -> None:
                        results.append(
                            all(get_inputs(count)) and all(predicate(substitution) for predicate in predicates)
                        )

                    stack.append(and_inputs)
                    for argument, child in zip(rhs.arguments, tree.children, strict=True):
                        if isinstance(argument, NonTerminalArgument):
                            stack.append((argument.origin, child))
            elif isinstance(task, FunctionType):
                # task is a function to execute
                task()

        if len(results) != 1:
            msg: str = "Number of results in contains_tree is not 1"
            raise ValueError(msg)

        return results.pop()
