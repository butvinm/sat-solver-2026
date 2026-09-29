import unittest

from propagate_test import make_solver
from solver import Solver
from utils import lit_from_dimacs

# Формула, где встречаются все переменные x1..x5.
CLAUSES = [[1, 2, 3], [-2, 4], [3, -5], [-1, 5]]
NUM_VARS = 5


class ChooseLiteralTest(unittest.TestCase):
    def assert_valid_choice(self, s: Solver, lit: int | None) -> None:
        """lit - настоящий литерал формулы, и его переменная не означена."""
        self.assertIsNotNone(lit, "вернулся None, хотя есть неозначенные переменные")
        assert lit is not None
        self.assertIsInstance(lit, int)
        self.assertGreaterEqual(lit, 2, f"литерал {lit}: переменные нумеруются с 1, литералы 0 и 1 не используются")
        self.assertLess(lit, s.formula.num_lits, f"литерал {lit} за пределами формулы")
        self.assertEqual(s.values[lit], 0, f"литерал {lit} уже означен")

    def decide_all(self, s: Solver) -> None:
        """Делать решения по choose_literal, пока он не вернёт None (не больше NUM_VARS шагов)."""
        for _ in range(NUM_VARS):
            lit = s.choose_literal()
            self.assert_valid_choice(s, lit)
            assert lit is not None
            s.decide(lit)
        self.assertIsNone(s.choose_literal(), f"все {NUM_VARS} переменных означены, а вернулся не None")

    def assign_all(self, s: Solver) -> None:
        for v in range(1, NUM_VARS + 1):
            s.assign(lit_from_dimacs(v))

    def test_fresh_solver(self) -> None:
        s = make_solver(CLAUSES)
        self.assert_valid_choice(s, s.choose_literal())

    def test_skips_assigned(self) -> None:
        s = make_solver(CLAUSES)
        for x in (1, -2, 3, 4):
            s.assign(lit_from_dimacs(x))
        lit = s.choose_literal()
        self.assert_valid_choice(s, lit)
        self.assertEqual(lit >> 1, 5)

    def test_all_assigned_returns_none(self) -> None:
        s = make_solver(CLAUSES)
        self.assign_all(s)
        self.assertIsNone(s.choose_literal())

    def test_all_assigned_negative_returns_none(self) -> None:
        # values[2v] == -1 - это тоже означенная переменная.
        s = make_solver(CLAUSES)
        for v in range(1, NUM_VARS + 1):
            s.assign(lit_from_dimacs(-v))
        self.assertIsNone(s.choose_literal())

    def test_does_not_change_state(self) -> None:
        s = make_solver(CLAUSES)
        s.assign(lit_from_dimacs(1))
        values, trail = list(s.values), list(s.trail)
        s.choose_literal()
        self.assertEqual(s.values, values)
        self.assertEqual(s.trail, trail)
        self.assertEqual(s.level(), 0)

    def test_decide_until_none(self) -> None:
        # Решения по choose_literal означивают все переменные ровно за NUM_VARS шагов.
        s = make_solver(CLAUSES)
        self.decide_all(s)
        self.assertEqual(sorted(lit >> 1 for lit in s.trail), list(range(1, NUM_VARS + 1)))

    def test_after_full_backtrack(self) -> None:
        s = make_solver(CLAUSES)
        self.decide_all(s)
        s.backtrack(0)
        self.assert_valid_choice(s, s.choose_literal())

    def test_after_partial_backtrack(self) -> None:
        # После отката на уровень 2 означены ровно две переменные, выбирать нужно из остальных.
        s = make_solver(CLAUSES)
        self.decide_all(s)
        s.backtrack(2)
        kept = {lit >> 1 for lit in s.trail}
        self.assertEqual(len(kept), 2)
        lit = s.choose_literal()
        self.assert_valid_choice(s, lit)
        assert lit is not None
        self.assertNotIn(lit >> 1, kept)


if __name__ == "__main__":
    unittest.main()
