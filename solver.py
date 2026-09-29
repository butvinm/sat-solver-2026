import sys
from threading import Event
from typing import Any

from utils import SATSolverResult, lit_to_dimacs, load_formula


class Solver:
    def __init__(self, filename: str, sigkill: Event) -> None:
        self.sigkill = sigkill
        self.formula = load_formula(filename)
        self.num_vars = self.formula.num_vars
        num_lits = self.formula.num_lits

        # Присваивание: values[ℓ] = 1 (истинен), -1 (ложен), 0 (не означен).
        # Хранится и для ℓ, и для ¬ℓ: values[ℓ] == -values[ℓ ^ 1].
        self.values = [0] * num_lits

        # Трейл — означенные литералы в порядке присваивания.
        # trail[:propagated] уже распространены, trail[propagated:] — ещё нет.
        self.trail: list[int] = []
        self.propagated = 0

        # control[i] — позиция в trail решения уровня i + 1;
        # текущий уровень решения = len(control).
        self.control: list[int] = []

        self.model: list[int] | None = None

        self.preprocess()
        self.build_occurrences()

    def preprocess(self) -> None:
        """
        Разбор дизъюнктов формулы:
          clauses          — дизъюнкты длины ≥ 2, без повторов литералов и тавтологий (a ∨ ¬a ∨ ...)
          units            — литералы единичных дизъюнктов
          has_empty_clause — во входе есть пустой дизъюнкт (формула невыполнима)
        """
        self.clauses: list[list[int]] = []
        self.units: list[int] = []
        self.has_empty_clause = False
        for clause in self.formula.clauses:
            lits = set(clause)
            if not lits:
                self.has_empty_clause = True
            elif any(lit ^ 1 in lits for lit in lits):
                continue
            elif len(lits) == 1:
                self.units.append(lits.pop())
            else:
                self.clauses.append(list(lits))

    def level(self) -> int:
        return len(self.control)

    def assign(self, lit: int) -> None:
        """Сделать ℓ истинным на текущем уровне."""
        self.values[lit] = 1
        self.values[lit ^ 1] = -1
        self.trail.append(lit)

    def decide(self, lit: int) -> None:
        """Открыть новый уровень решения и сделать ℓ истинным."""
        self.control.append(len(self.trail))
        self.assign(lit)

    def decision(self, level: int) -> int:
        """Литерал-решение уровня level (1 ≤ level ≤ self.level())."""
        return self.trail[self.control[level - 1]]

    def backtrack(self, level: int) -> None:
        """Отменить все присваивания уровней > level."""
        if level >= len(self.control):
            return

        values, trail = self.values, self.trail
        start = self.control[level]
        for i in range(start, len(trail)):
            lit = trail[i]
            values[lit] = 0
            values[lit ^ 1] = 0

        del trail[start:]
        del self.control[level:]
        self.propagated = start

    def save_model(self) -> None:
        values = self.values
        self.model = [
            lit_to_dimacs(2 * v if values[2 * v] > 0 else 2 * v + 1)
            for v in range(1, self.num_vars + 1)
        ]

    def build_occurrences(self) -> None:
        self.occurrences: list[list[list[int]]] = [
            [] for _ in range(self.formula.num_lits)
        ]
        for c in self.clauses:
            for lit in c:
                self.occurrences[lit].append(c)

    def build_watches(self) -> None:
        num_lits = self.formula.num_lits
        self.binary: list[list[int]] = [[] for _ in range(num_lits)]
        # Элемент watches[ℓ] - пара [блокер, дизъюнкт]; список, а не кортеж, чтобы блокер можно было заменить.
        self.watches: list[list[list[Any]]] = [[] for _ in range(num_lits)]
        for c in self.clauses:
            if len(c) == 2:
                self.binary[c[0]].append(c[1])
                self.binary[c[1]].append(c[0])
            else:
                self.watches[c[0]].append([c[1], c])
                self.watches[c[1]].append([c[0], c])

    def propagate(self) -> bool:
        """
        UnitPropagate: распространить литералы trail[propagated:].
        Возвращает True, если найден конфликт (все литералы дизъюнкта ложны).
        """
        values = self.values
        trail = self.trail
        while self.propagated < len(self.trail):
            l = trail[self.propagated]
            for clause in self.occurrences[l ^ 1]:
                has_true = False
                first_unassigned: int | None = None
                has_second_unassigned = False
                for k in clause:
                    v = values[k]
                    if v == 1:
                        has_true = True
                        break  # если есть хоть один истинный, весь клоз выполнен - пропускам
                    elif v == 0:
                        if first_unassigned is None:
                            first_unassigned = k
                        else:
                            has_second_unassigned = True
                            break

                if has_true or has_second_unassigned:
                    continue
                elif first_unassigned is not None:
                    self.assign(first_unassigned)
                else:
                    return True

            self.propagated += 1

        return False

    def choose_literal(self) -> int | None:
        """
        ChooseLiteral: литерал для следующего решения или None, если все
        переменные означены.
        """
        values = self.values
        for l in range(2, len(values), 2):
            v = values[l]
            if v == 0:
                return l

        return None

    def solve(self) -> SATSolverResult:
        if self.has_empty_clause:
            return SATSolverResult.UNSAT

        values = self.values
        for u in self.units:
            v = values[u]
            if v == 0:
                self.assign(u)
            elif v == 1:
                continue
            else:
                return SATSolverResult.UNSAT

        while not self.sigkill.is_set():
            L = self.level()
            if self.propagate():
                if L == 0:
                    return SATSolverResult.UNSAT

                l = self.decision(L)
                self.backtrack(L - 1)
                self.assign(l ^ 1)
            else:
                l = self.choose_literal()
                if l is None:
                    self.save_model()
                    return SATSolverResult.SAT

                self.decide(l)

        return SATSolverResult.UNKNOWN


if __name__ == "__main__":
    result = Solver(sys.argv[1], Event()).solve()
    if result == SATSolverResult.SAT:
        print("sat")
    elif result == SATSolverResult.UNSAT:
        print("unsat")
    else:
        print("unknown")
