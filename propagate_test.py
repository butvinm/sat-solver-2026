import os
import tempfile
import unittest
from threading import Event

from solver import Solver
from utils import lit_from_dimacs


def make_solver(clauses: list[list[int]]) -> Solver:
    """Solver для формулы, заданной дизъюнктами в нотации DIMACS (3 - это x_3, -3 - это ¬x_3)."""
    num_vars = max((abs(x) for c in clauses for x in c), default=0)
    lines = [f"p cnf {num_vars} {len(clauses)}"]
    lines += [" ".join(map(str, c)) + " 0" for c in clauses]
    fd, path = tempfile.mkstemp(suffix=".cnf")
    try:
        with os.fdopen(fd, "w") as f:
            f.write("\n".join(lines) + "\n")
        return Solver(path, Event())
    finally:
        os.remove(path)


class PropagateTest(unittest.TestCase):
    def value(self, s: Solver, x: int) -> int:
        """Значение литерала x (DIMACS): 1, -1 или 0."""
        return s.values[lit_from_dimacs(x)]

    def assign(self, s: Solver, *xs: int) -> None:
        for x in xs:
            s.assign(lit_from_dimacs(x))

    def assert_consistent(self, s: Solver) -> None:
        """Каждая переменная в trail не больше одного раза, values совпадает с trail."""
        vars_in_trail = [lit >> 1 for lit in s.trail]
        self.assertEqual(len(vars_in_trail), len(set(vars_in_trail)), f"повтор в trail: {s.trail}")
        for lit in s.trail:
            self.assertEqual(s.values[lit], 1)
            self.assertEqual(s.values[lit ^ 1], -1)
        assigned = sum(1 for v in s.values if v == 1)
        self.assertEqual(assigned, len(s.trail))

    def test_empty_trail(self) -> None:
        s = make_solver([[1, 2], [-1, 3]])
        self.assertIs(s.propagate(), False)
        self.assertEqual(s.trail, [])

    def test_binary_clause_becomes_unit(self) -> None:
        # (x1 ∨ x2), x1 = false -> x2 = true
        s = make_solver([[1, 2]])
        self.assign(s, -1)
        self.assertIs(s.propagate(), False)
        self.assertEqual(self.value(s, 2), 1)
        self.assert_consistent(s)

    def test_long_clause_becomes_unit(self) -> None:
        # (x1 ∨ x2 ∨ x3 ∨ x4), первые три ложны -> x4 = true
        s = make_solver([[1, 2, 3, 4]])
        self.assign(s, -1, -2, -3)
        self.assertIs(s.propagate(), False)
        self.assertEqual(self.value(s, 4), 1)
        self.assert_consistent(s)

    def test_unit_literal_is_not_the_last_one(self) -> None:
        # Неозначенный литерал стоит в середине дизъюнкта: выводиться должен именно он.
        s = make_solver([[1, 2, 3]])
        self.assign(s, -1, -3)
        self.assertIs(s.propagate(), False)
        self.assertEqual(self.value(s, 2), 1)
        self.assert_consistent(s)

    def test_two_unassigned_no_inference(self) -> None:
        s = make_solver([[1, 2, 3]])
        self.assign(s, -1)
        self.assertIs(s.propagate(), False)
        self.assertEqual(self.value(s, 2), 0)
        self.assertEqual(self.value(s, 3), 0)
        self.assert_consistent(s)

    def test_satisfied_clause_is_skipped(self) -> None:
        # (x1 ∨ x2 ∨ x3) уже выполнен через x1, поэтому ¬x2 не должен выводить x3.
        s = make_solver([[1, 2, 3]])
        self.assign(s, 1, -2)
        self.assertIs(s.propagate(), False)
        self.assertEqual(self.value(s, 3), 0)
        self.assert_consistent(s)

    def test_clauses_with_true_literal_are_ignored(self) -> None:
        # x1 = true не должен ничего выводить из дизъюнктов, где x1 входит без отрицания.
        s = make_solver([[1, 2], [1, 3, 4]])
        self.assign(s, 1)
        self.assertIs(s.propagate(), False)
        self.assertEqual(s.trail, [lit_from_dimacs(1)])

    def test_chain(self) -> None:
        # x1 -> x2 -> x3 -> x4: литералы, выведенные во время propagate, тоже распространяются.
        s = make_solver([[-1, 2], [-2, 3], [-3, 4]])
        self.assign(s, 1)
        self.assertIs(s.propagate(), False)
        for x in (2, 3, 4):
            self.assertEqual(self.value(s, x), 1, f"x{x}")
        self.assert_consistent(s)

    def test_same_literal_implied_twice(self) -> None:
        # x2 выводится из двух дизъюнктов, но в trail должен попасть один раз.
        s = make_solver([[-1, 2], [-3, 2]])
        self.assign(s, 1, 3)
        self.assertIs(s.propagate(), False)
        self.assertEqual(self.value(s, 2), 1)
        self.assert_consistent(s)

    def test_conflict_all_false(self) -> None:
        s = make_solver([[1, 2, 3]])
        self.assign(s, -1, -2, -3)
        self.assertIs(s.propagate(), True)

    def test_conflict_after_inference(self) -> None:
        # x1 -> x2 и x1 -> ¬x2
        s = make_solver([[-1, 2], [-1, -2]])
        self.assign(s, 1)
        self.assertIs(s.propagate(), True)

    def test_conflict_at_end_of_chain(self) -> None:
        # x1 -> x2 -> x3, а (¬x1 ∨ ¬x3) запрещает x3
        s = make_solver([[-1, 2], [-2, 3], [-1, -3]])
        self.assign(s, 1)
        self.assertIs(s.propagate(), True)

    def test_propagated_pointer_reaches_end(self) -> None:
        s = make_solver([[-1, 2], [-2, 3]])
        self.assign(s, 1)
        s.propagate()
        self.assertEqual(s.propagated, len(s.trail))

    def test_second_call_does_nothing(self) -> None:
        s = make_solver([[-1, 2], [-2, 3]])
        self.assign(s, 1)
        s.propagate()
        trail = list(s.trail)
        self.assertIs(s.propagate(), False)
        self.assertEqual(s.trail, trail)

    def test_incremental(self) -> None:
        # Второй вызов распространяет только новые литералы.
        s = make_solver([[1, 2, 3]])
        self.assign(s, -1)
        self.assertIs(s.propagate(), False)
        self.assertEqual(self.value(s, 3), 0)
        self.assign(s, -2)
        self.assertIs(s.propagate(), False)
        self.assertEqual(self.value(s, 3), 1)
        self.assert_consistent(s)

    def test_after_backtrack(self) -> None:
        # Решение x1 ведёт к конфликту; после отката и вывода ¬x1 конфликта нет, x3 выводится.
        s = make_solver([[-1, 2], [-1, -2], [1, 3]])
        s.decide(lit_from_dimacs(1))
        self.assertIs(s.propagate(), True)
        s.backtrack(0)
        self.assertEqual(self.value(s, 2), 0)
        self.assign(s, -1)
        self.assertIs(s.propagate(), False)
        self.assertEqual(self.value(s, 3), 1)
        self.assert_consistent(s)

    def test_inferred_literals_belong_to_current_level(self) -> None:
        # Выводы после decide должны откатываться вместе с решением.
        s = make_solver([[-1, 2], [-2, 3]])
        s.decide(lit_from_dimacs(1))
        self.assertIs(s.propagate(), False)
        s.backtrack(0)
        self.assertEqual(s.trail, [])
        self.assertEqual(s.propagated, 0)
        for x in (1, 2, 3):
            self.assertEqual(self.value(s, x), 0, f"x{x}")


if __name__ == "__main__":
    unittest.main()
