from PropNode import *
from functools import reduce

class SAT:
    def __init__(self, wff: PropNode):
        self.wff = wff
        self.constraints = []

    # modify self.constraints directly
    def wff_to_CNF(self):
        # generate fresh variable name
        def generate_var(counter: int) -> (PropVariable, int):
            return PropVariable("tseitin_v{}".format(counter)), counter + 1

        # work for each node
        def helper(wff: PropNode, top: PropVariable, counter: int) -> (list, int, bool, PropVariable, bool, PropVariable):
            a = top
            if isinstance(wff.left, PropVariable): p, l = wff.left, False
            else: (p, counter), l = generate_var(counter), True
            if isinstance(wff.right, PropVariable): q, r = wff.right, False
            else: (q, counter), r = generate_var(counter), True
            if wff.op == PropEnum.OR:
                return [[a, PropNot(p)], [a, PropNot(q)], [p, q, PropNot(a)]], counter, l, p, r, q
            elif wff.op == PropEnum.AND:
                # return [PropOr(a, PropOr(PropNot(p), PropNot(q))),
                #         PropOr(p, PropNot(a)),
                #         PropOr(q, PropNot(a))], counter, l, p, r, q
                return [[a, PropNot(p), PropNot(q)], [p, PropNot(a)], [q, PropNot(a)]], counter, l, p, r, q
            else: #return [PropOr(a, p), PropOr(PropNot(p), PropNot(a))], counter, l, p, r, q
                return [[a, p], [PropNot(p), PropNot(a)]], counter, False, p, False, q

        def pre_order_traversal(top: PropNode, top_var: PropVariable, counter: int):
            if isinstance(top, PropVariable) or isinstance(top, PropConstant): return
            c, counter, l, l_n, r, r_n = helper(top, top_var, counter)
            self.constraints.extend(c)
            if l: pre_order_traversal(top.left, l_n, counter)
            if r: pre_order_traversal(top.right, r_n, counter)

        top_var, counter = generate_var(0)
        self.constraints = [[top_var]]
        pre_order_traversal(self.wff, top_var, counter)

class SATSolver:
    def __init__(self, delta = []):
        # assume CNF -> list of disjunctions clauses
        # assume variable name not equal to "."
        self.delta = [[clause, False] for clause in delta]
        self.conflicts = set()
        self.M = [] # decisions
        self.undecide_literals = reduce(lambda b, l: b.add(l) or b if PropNot(l) not in b else b, [l for clause in delta for l in clause], set())

    def update_delta(self, l, b):
        for i, [clause, _] in enumerate(self.delta):
            if l in clause: self.delta[i][1] = b

    def check_delta(self):
        for literal in self.M:
            if literal == ".": continue
            self.update_delta(literal, False)

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
                    self.update_delta(l, True)
                    # mark as decided
                    self.undecide_literals.discard(l)
                    return True
            return False

        def decide() -> bool:
            if len(self.undecide_literals) == 0: return False
            l = self.undecide_literals.pop()
            self.M.extend([".", l])
            self.update_delta(l, True)
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
            if len(self.conflicts) == 0: return False
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
            self.check_delta()
            return True

        # return True if failed
        # return False if not failed yet
        def fail() -> bool:
            return (len(self.conflicts) == 0) and ("." not in self.M)

        while not self.check_sat():
            if conflict():
                explain()
                if not backjump():
                    explain()
                    if fail():
                        return None
            if not propagate():
                decide()
                if fail():
                    return None

        if self.check_sat():
            ret = {l: True for l in [l if isinstance(l, PropVariable) else PropNot(l) for clause, _ in self.delta for l in clause]}
            for l in self.M:
                if isinstance(l, PropFunction): ret[PropNot(l)] = False
            return ret



if __name__ == "__main__":
    c = PropOr(PropVariable("a"), PropVariable("b"))
    s = SAT(c)
    s.wff_to_CNF()
    solver = SATSolver(s.constraints)
    print(solver.solve())

    c = PropAnd(PropVariable("a"), PropVariable("b"))
    s = SAT(c)
    s.wff_to_CNF()
    solver = SATSolver(s.constraints)
    print(solver.solve())

    c = PropNot(PropVariable("a"))
    s = SAT(c)
    s.wff_to_CNF()
    solver = SATSolver(s.constraints)
    print(solver.solve())

    c1 = PropAnd(PropVariable("a"), PropVariable("b"))
    c2 = PropOr(PropVariable("c"), PropVariable("d"))
    c3 = PropNot(PropVariable("e"))
    c4 = PropAnd(c1, c2)
    c5 = PropAnd(c3, c4)
    s = SAT(c5)
    s.wff_to_CNF()
    solver = SATSolver(s.constraints)
    print(solver.solve())

    c1 = [PropVariable("1")]
    c2 = [PropVariable("1"), PropNot(PropVariable("2"))]
    c3 = [PropVariable("1"), PropNot(PropVariable("3"))]
    c4 = [PropVariable("2"), PropVariable("3"), PropNot(PropVariable("1"))]
    s = SATSolver([c1, c2, c3, c4])
    print(s.solve())

    c1 = [PropVariable("1")]
    c2 = [PropNot(PropVariable("1")), PropVariable("2")]
    c3 = [PropNot(PropVariable("3")), PropVariable("4")]
    c4 = [PropNot(PropVariable("5")), PropNot(PropVariable("6"))]
    c5 = [PropNot(PropVariable("1")), PropNot(PropVariable("5")), PropVariable("7")]
    c6 = [PropNot(PropVariable("2")), PropNot(PropVariable("5")), PropVariable("6"), PropNot(PropVariable("7"))]
    s = SATSolver([c1, c2, c3, c4, c5, c6])
    print(s.solve())
    c1 = [PropVariable("1")]
    c2 = [PropNot(PropVariable("1"))]
    s = SATSolver([c1, c2])
    print(s.solve())

    s, a, b = PropVariable("s"), PropVariable("a"), PropVariable("b")
    c1 = PropAnd(PropAnd(s, PropNot(b)), PropNot(a))
    c2 = PropAnd(PropAnd(PropNot(s), b), PropNot(a))
    c3 = PropAnd(PropAnd(PropNot(s), PropNot(b)), a)
    c4 = PropOr(c1, c2)
    c5 = PropOr(c3, c4)
    s = SAT(c5)
    s.wff_to_CNF()
    solver = SATSolver(s.constraints)
    print(solver.solve())

    p, q, r, s = PropVariable("p"), PropVariable("q"), PropVariable("r"), PropVariable("s")
    a = PropAnd(p, q)
    b = PropOr(a, PropNot(r))
    c = PropOr(b, PropNot(s))
    d = PropOr(r, PropNot(s))
    e = PropOr(d, PropNot(p))
    f = PropOr(e, PropNot(s))
    g = PropOr(c, PropNot(f))
    s = SAT(g)
    s.wff_to_CNF()
    solver = SATSolver(s.constraints)
    print(solver.solve())
