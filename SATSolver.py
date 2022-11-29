from PropNode import *
from functools import reduce

class SATSolver:
    def __init__(self, delta = []):
        # assume CNF -> list of disjunctions clauses
        # assume variable name not equal to "."
        self.delta = [[clause, False] for clause in delta]
        self.conflicts = set()
        self.M = [] # decisions
        self.undecide_literals = reduce(lambda b, l: b.add(l) or b if PropNot(l) not in b else b, [l for clause in delta for l in clause], set())

    def update_delta(self, l):
        for i, [clause, _] in enumerate(self.delta):
            if l in clause: self.delta[i][1] = True

    def find_level(self, l):
        cnt = 0
        for literal in self.M:
            if literal == l: return cnt
            if literal == ".": cnt += 1
        return None

    def check_sat(self):
        return all([b for _, b in self.delta])

    def solve(self):
        # return false if not propagated
        # return true if propagated
        def propagate() -> bool:
            for clause, solved in self.delta:
                if solved: continue
                l = None
                for literal in clause:
                    # not assigned to True
                    if literal not in self.M:
                        # unassigned
                        if PropNot(literal) not in self.M:
                            # more than one unassigned literal
                            if l:
                                l = None
                                break
                            else: l = literal
                        # already assigned to False -> fulfill requirements
                        else: continue
                    # already assigned to True -> next clause
                    else:
                        l = None
                        break
                if l:
                    self.M.append(l)
                    # set as satisfied
                    self.update_delta(l)
                    # mark as decided
                    self.undecide_literals.discard(l)
                    return True
            return False

        def decide() -> bool:
            if len(self.undecide_literals) == 0: return False
            l = self.undecide_literals.pop()
            self.M.extend([".", l])
            self.update_delta(l)
            return True

        def conflict() -> bool:
            if len(self.conflicts) != 0: return False
            for clause, _ in self.delta:
                find_conflict = True
                for literal in clause:
                    # no conflict if not l not in M
                    if PropNot(literal) not in self.M:
                        find_conflict = False
                        break
                if find_conflict:
                    self.conflicts = set(clause)
                    return True
            return False

        def explain():
            for literal in self.conflicts:
                level_literal = self.M.index(PropNot(literal))
                for clause, _ in self.delta:
                    if PropNot(literal) not in clause: continue
                    need_break = False
                    # not l in the clause
                    for l in clause:
                        need_break = False
                        if PropNot(l) == literal: continue
                        if PropNot(l) not in self.M:
                            need_break = True
                            break
                        level = self.M.index(PropNot(l))
                        if level >= level_literal:
                            need_break = True
                            break
                    if need_break: continue
                    self.conflicts.update(clause)
                    self.conflicts.discard(literal)
                    self.conflicts.discard(PropNot(literal))
                    return

        def backjump():
            levels = [(self.find_level(PropNot(l)), l) for l in self.conflicts]
            levels.sort()
            self.conflicts = set()
            (max_level, l), i = levels[-1], 0
            for lev, _ in levels:
                if i < lev: i += 1
            if i == max_level: return False
            ind = [i for i, n in enumerate(self.M) if n == "."][i - 1]
            self.M = self.M[:ind]
            self.M.append(l)
            for l in self.M: self.update_delta(l)
            return True

        # return True if failed
        # return False if not failed yet
        def fail() -> bool:
            return (len(self.conflicts) == 0) and ("." not in self.M)

        while not self.check_sat():
            propagate()
            if not decide():
                if fail():
                    return None
            if conflict():
                while not backjump():
                    explain()
        if self.check_sat():
            ret = {l: True for l in [l if isinstance(l, PropVariable) else PropNot(l) for clause, _ in self.delta for l in clause]}
            for l in self.M:
                if isinstance(l, PropFunction): ret[PropNot(l)] = False
            return ret



if __name__ == "__main__":
    # c1 = [PropVariable("1")]
    # c2 = [PropNot(PropVariable("1")), PropVariable("2")]
    # c3 = [PropNot(PropVariable("3")), PropVariable("4")]
    # c4 = [PropNot(PropVariable("5")), PropNot(PropVariable("6"))]
    # c5 = [PropNot(PropVariable("1")), PropNot(PropVariable("5")), PropVariable("7")]
    # c6 = [PropNot(PropVariable("2")), PropNot(PropVariable("5")), PropVariable("6"), PropNot(PropVariable("7"))]
    # s = SATSolver([c1, c2, c3, c4, c5, c6])
    # # s.M = [PropVariable("1"), PropVariable("2"), ".", PropVariable("3"), PropVariable("4"), ".", PropVariable("5"), PropNot(PropVariable("6")), PropVariable("7")]
    # print(s.solve())
    c1 = [PropVariable("1")]
    c2 = [PropNot(PropVariable("1"))]
    s = SATSolver([c1, c2])
    print(s.solve())
