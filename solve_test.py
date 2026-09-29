import itertools
import os
import random
import unittest
from threading import Event, Thread

from propagate_test import make_solver
from solver import Solver
from utils import SATSolverResult, lit_to_dimacs

TIMEOUT = 5.0
TESTS_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tests")


def brute_force_sat(clauses: list[list[int]], num_vars: int) -> bool:
    for bits in itertools.product((False, True), repeat=num_vars):
        if all(any(bits[abs(x) - 1] == (x > 0) for x in c) for c in clauses):
            return True
    return False


class SolveTest(unittest.TestCase):
    def run_solve(self, s: Solver) -> SATSolverResult:
        """solve() в отдельном потоке: если не уложился в TIMEOUT, тест падает, а не зависает."""
        result: list[SATSolverResult] = []
        error: list[BaseException] = []

        def target() -> None:
            try:
                result.append(s.solve())
            except BaseException as e:
                error.append(e)

        thread = Thread(target=target, daemon=True)
        thread.start()
        thread.join(TIMEOUT)
        if thread.is_alive():
            s.sigkill.set()
            thread.join(1.0)
            self.fail(f"solve() не завершился за {TIMEOUT} с")
        if error:
            raise error[0]
        return result[0]

    def assert_model(self, s: Solver, clauses: list[list[int]]) -> None:
        """model - полное присваивание, выполняющее каждый дизъюнкт."""
        self.assertIsNotNone(s.model, "при SAT нужно вызвать save_model()")
        assert s.model is not None
        model = set(s.model)
        for v in range(1, s.num_vars + 1):
            self.assertTrue((v in model) != (-v in model), f"x{v}: в модели должно быть ровно одно из {v} и {-v}")
        for c in clauses:
            self.assertTrue(any(x in model for x in c), f"дизъюнкт {c} ложен в модели {s.model}")

    def check(self, clauses: list[list[int]], expected: SATSolverResult) -> None:
        s = make_solver(clauses)
        self.assertEqual(self.run_solve(s), expected)
        if expected == SATSolverResult.SAT:
            self.assert_model(s, clauses)

    # Без поиска

    def test_empty_clause(self) -> None:
        self.check([[1, 2], []], SATSolverResult.UNSAT)

    def test_contradicting_units(self) -> None:
        self.check([[1], [2, 3], [-1]], SATSolverResult.UNSAT)

    def test_duplicate_unit(self) -> None:
        self.check([[1], [1], [-1, 2]], SATSolverResult.SAT)

    def test_units_propagate_to_conflict(self) -> None:
        # x1 -> x2, x1 -> ¬x2 на уровне 0
        self.check([[1], [-1, 2], [-1, -2]], SATSolverResult.UNSAT)

    def test_sigkill_already_set(self) -> None:
        s = make_solver([[1, 2]])
        s.sigkill.set()
        self.assertEqual(s.solve(), SATSolverResult.UNKNOWN)

    # С поиском

    def test_single_clause(self) -> None:
        self.check([[1, 2, 3]], SATSolverResult.SAT)

    def test_first_guess_is_wrong(self) -> None:
        # x1 = true ведёт к конфликту (x2 и ¬x2), выполнимо только при x1 = false.
        self.check([[-1, 2], [-1, -2], [1, 3]], SATSolverResult.SAT)
        # x1 -> x2 -> x3, но истинной может быть только одна переменная: x1 и x2 обязаны быть ложны.
        self.check([[-1, -2], [-2, -3], [-3, -1], [-1, 2], [-2, 3]], SATSolverResult.SAT)

    def test_all_four_combinations_forbidden(self) -> None:
        # Нужен откат через два уровня.
        self.check([[1, 2], [1, -2], [-1, 2], [-1, -2]], SATSolverResult.UNSAT)

    def test_pigeonhole_3_into_2(self) -> None:
        # 3 голубя, 2 клетки: p(i, j) = голубь i в клетке j, переменная 2 * (i - 1) + j.
        p = lambda i, j: 2 * (i - 1) + j
        clauses = [[p(i, 1), p(i, 2)] for i in range(1, 4)]
        clauses += [[-p(i, j), -p(k, j)] for j in (1, 2) for i in range(1, 4) for k in range(i + 1, 4)]
        self.check(clauses, SATSolverResult.UNSAT)

    def test_random_against_brute_force(self) -> None:
        # Останавливается на первой формуле с неверным ответом и печатает её.
        rng = random.Random(2026)
        for n in range(3, 11):
            for _ in range(30):
                m = rng.randint(n, 6 * n)
                clauses = [[v if rng.random() < 0.5 else -v for v in rng.sample(range(1, n + 1), 3)] for _ in range(m)]
                expected = SATSolverResult.SAT if brute_force_sat(clauses, n) else SATSolverResult.UNSAT
                try:
                    self.check(clauses, expected)
                except Exception as e:
                    raise AssertionError(f"формула {clauses}") from e

    # Файлы из tests/

    def test_small_files(self) -> None:
        cases = [
            ("sat-dpll/3cnf-10-45_1.cnf", SATSolverResult.SAT),
            ("unsat-dpll/3cnf-10-65_1.cnf", SATSolverResult.UNSAT),
        ]
        for name, expected in cases:
            with self.subTest(name=name):
                s = Solver(os.path.join(TESTS_DIR, name), Event())
                self.assertEqual(self.run_solve(s), expected)
                if expected == SATSolverResult.SAT:
                    self.assert_model(s, [[lit_to_dimacs(x) for x in c] for c in s.formula.clauses])


if __name__ == "__main__":
    unittest.main()
