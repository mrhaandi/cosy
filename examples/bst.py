from src.cosy.core.tree import Tree
from src.cosy.core.types import Group, DataGroup
from src.cosy.core import SpecificationBuilder, Synthesizer, Constructor, Literal, Var

import time


class BST_Repository:
    """
            Repository for binary search trees (BSTs) with string-labeled nodes
    """

    def __init__(self, max_height: int, labels: list[str]):
        self.max_height = max_height
        self.labels = labels

    @staticmethod
    def is_sorted(lst: list[str]) -> bool:
        sorted_lst = sorted(lst)
        return lst == sorted_lst




    def specification(self):
        heights = DataGroup("height", range(0, self.max_height + 1))
        labels = DataGroup("label", self.labels)

        return {
            "Node": SpecificationBuilder()
            .parameter("l", labels)
            .suffix(Constructor("BST", Constructor("height", Literal(0)) & Constructor("height", Literal(None)) & Constructor("label", Var("l")) & Constructor("label", Literal(None)))),

            "Fork": SpecificationBuilder()
            .parameter("h1", heights)
            .parameter("h2", heights)
            .parameter("h", heights, lambda vs: [max(vs["h1"], vs["h2"]) + 1])
            .parameter("l", labels)
            .argument("left", Constructor("BST", Constructor("height", Var("h1")) & Constructor("label", Literal(None))))
            .argument("right", Constructor("BST", Constructor("height", Var("h2")) & Constructor("label", Literal(None))))
            .constraint(lambda v: self.is_sorted(v["left"].interpret(self.inorder_traverse_algebra()) + [v["l"]] + v["right"].interpret(self.inorder_traverse_algebra())))
            .suffix(Constructor("BST", Constructor("height", Var("h")) & Constructor("height", Literal(None)) & Constructor("label", Literal(None))))
        }

    def pretty_term_algebra(self):
        return {
            "Node": lambda l: f"Node ({l})",
            "Fork": lambda h1, h2, h, l, left, right: f"Fork ({l}) ({left}) ({right})"
        }

    def inorder_traverse_algebra(self):
        return {
            "Node": lambda l: [l],
            "Fork": lambda h1, h2, h, l, left, right: left + [l] + right
        }




if __name__ == "__main__":

    repo = BST_Repository(5,["A", "B", "C"])

    target = Constructor("BST", Constructor("height", Literal(None)) & Constructor("label", Literal(None)))
    synthesizer = Synthesizer(repo.specification(), {})

    start_time = time.time()
    solution_space = synthesizer.construct_solution_space(target).prune()
    end_time = time.time()

    print(f"SolutionSpace construction took {end_time - start_time:.5f} seconds.")

    start_time = time.time()
    terms = solution_space.enumerate_trees(target, max_count=50)
    end_time = time.time()

    print(f"Term-Generator construction for resolution took {end_time - start_time:.5f} seconds.")

    start_time = time.time()
    i = 0
    for term in terms:
        print(term.interpret(repo.pretty_term_algebra()))
        i += 1
    end_time = time.time()
    print(f"Resolution and printing of {i} terms took {end_time - start_time:.2f} seconds.")


