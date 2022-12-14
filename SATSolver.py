from PropNode import *
from collections import deque

class SAT:
    def __init__(self, wff: PropNode):
        self.wff = wff
        self.constraints = []
        self.original_vars = set()
        self.pass_to_sat_var = set()
        self.pass_to_sat_clause = set()
        self.assign = dict()

    # modify self.constraints directly
    def wff_to_CNF(self):
        # generate fresh variable name
        def generate_var(counter: int) -> (PropVariable, int):
            return PropVariable("t{}".format(counter)), counter + 1

        # work for each node
        def helper(node: PropNode, counter: int) -> (PropVariable, int):
            if isinstance(node, PropVariable) or isinstance(node, PropConstant):
                self.original_vars.add(node)
                return node, counter

            p, counter = helper(node.left, counter)
            if node.right: q, counter = helper(node.right, counter)

            a, counter = generate_var(counter)

            if node.op == PropEnum.NOT:
                self.constraints.append([a, p])
                self.constraints.append([PropNot(p), PropNot(a)])
            elif node.op == PropEnum.AND:
                self.constraints.append([a, PropNot(p), PropNot(q)])
                self.constraints.append([p, PropNot(a)])
                self.constraints.append([q, PropNot(a)])
            elif node.op == PropEnum.OR:
                self.constraints.append([PropNot(a), p, q])
                self.constraints.append([a, PropNot(p)])
                self.constraints.append([a, PropNot(q)])
            else:
                raise Exception("invalid input node")

            return a, counter

        t, _ = helper(self.wff, 0)
        self.constraints.append([t])

    # update inputs to the SAT solver based on self.constraints
    def prepare_solver(self):
        # return the positive literal
        def to_positive_literal(lit) -> PropNode:
            if isinstance(lit, PropVariable): return lit
            return PropNot(lit)

        self.pass_to_sat_clause = set([frozenset(c) for c in self.constraints])
        self.pass_to_sat_var = set(reduce(lambda b, l: b.add(to_positive_literal(l)) or b, [l for clause in self.constraints for l in clause], set()))

    # update assignment to the original input wff
    def assign_valid(self, assignment):
        if not assignment:
            self.assign = None
            return
        for atom, val in assignment.items():
            if atom in self.original_vars:
                self.assign[atom] = val

class SATSolver:
    def __init__(self, delta, vars):
        self.delta = delta
        self.vars = vars
        self.learnts = set()
        self.M = dict.fromkeys(list(self.vars), None)
        self.curr_level = 0
        self.nodes = dict((k, ImplicationNode(k, None)) for k in list(self.vars))
        self.branching_vars = set()
        self.branching_hist = dict()
        self.propagate_hist = dict()
        self.branching_cnt = 0

    def solve(self) -> dict:
        # return the positive literal
        def to_positive_literal(lit) -> PropNode:
            if isinstance(lit, PropVariable): return lit
            return PropNot(lit)

        # update the implication graph
        def update_implication_graph(var, clause=None):
            node = self.nodes[var]
            node.value = self.M[var]
            node.level = self.curr_level

            if clause:
                for v in [to_positive_literal(literal) for literal in clause if to_positive_literal(literal) != var]:
                    node.parents.append(self.nodes[v])
                    self.nodes[v].children.append(node)
                node.clause = clause

        # performing unit propagation rule
        def unit_propagate() -> frozenset:
            def compute_value(literal) -> bool:
                value = self.M[to_positive_literal(literal)]
                return value if value == None else value ^ (isinstance(literal, PropFunction))

            while True:
                propagate_deque = deque()
                self.delta.union(self.learnts)
                for clause in [x for x in self.delta]:
                    values = list(map(compute_value, clause))
                    val = None if None in values else max(values)
                    if val == True: continue
                    if val == False: return clause
                    else:
                        values, unassigned_lit = [], None

                        for literal in clause:
                            values.append(compute_value(literal))
                            unassigned_lit = literal if values[-1] == None else unassigned_lit

                        if not ((values.count(False) == len(clause) - 1 and values.count(None) == 1) or (len(clause) == 1 and values.count(None) == 1)): continue
                        if (unassigned_lit, clause) not in propagate_deque: propagate_deque.append((unassigned_lit, clause))
                if not propagate_deque: return None

                for propagate_lit, clause in propagate_deque:
                    propagate_var = to_positive_literal(propagate_lit)
                    self.M[propagate_var] = True if isinstance(propagate_lit, PropVariable) else False
                    update_implication_graph(propagate_var, clause)
                    if self.curr_level in self.propagate_hist.keys(): self.propagate_hist[self.curr_level].append(propagate_lit)

        # find cause of the conflict
        def explain(conflict_clause) -> (int, frozenset):
            if self.curr_level == 0: return -1, None

            literal_backups, literal_decided, literal_curr_lvl, literals_prev_lvls = conflict_clause, set(), set(), set()

            while True:
                for lit in literal_backups:
                    if self.nodes[to_positive_literal(lit)].level == self.curr_level: literal_curr_lvl.add(lit)
                    else: literals_prev_lvls.add(lit)

                if len(literal_curr_lvl) == 1: break

                for v in reversed([self.branching_hist[self.curr_level]] + list(self.propagate_hist[self.curr_level])):
                    if v in clause or PropNot(v) in clause:
                        literal_decided.add(to_positive_literal(v))
                        pool_clause = self.nodes[to_positive_literal(v)].clause
                        literal_curr_lvl = set([x for x in clause if to_positive_literal(x) != to_positive_literal(v)])
                        literal_backups = [l for l in pool_clause if to_positive_literal(l) not in literal_decided] if pool_clause is not None else []
                        break

            learnt = frozenset([l for l in literal_curr_lvl.union(literals_prev_lvls)])

            if literals_prev_lvls: level = max([self.nodes[to_positive_literal(x)].level for x in literals_prev_lvls])
            else: level = self.curr_level - 1

            return level, learnt

        # backjumping to the cause and reassign
        def backjump(level):
            for var, node in self.nodes.items():
                if node.level <= level: node.children[:] = [child for child in node.children if child.level <= level]
                else: node.value, node.level, node.parents, node.children, node.clause, self.M[node.variable] = None, -1, [], [], None, None

            self.branching_vars = set([var for var in self.vars if (self.M[var] != None and len(self.nodes[var].parents) == 0)])

            for k in self.propagate_hist.keys():
                if k <= level: continue
                del self.branching_hist[k]
                del self.propagate_hist[k]

        # start the loop of solving
        while not (all(var in self.M for var in self.vars) and not any(var for var in self.vars if self.M[var] == None)):
            conflict_clause = unit_propagate()
            if conflict_clause is not None:
                lvl, learnt = explain(conflict_clause)
                if lvl < 0: return None
                self.learnts.add(learnt)
                backjump(lvl)
                self.curr_level = lvl
            elif (all(var in self.M for var in self.vars) and not any(var for var in self.vars if self.M[var] == None)):
                break
            else:
                self.curr_level += 1
                self.branching_cnt += 1
                backjump_var = next(filter(lambda v: v in self.M and self.M[v] == None, self.vars))
                self.M[backjump_var] = True
                self.branching_vars.add(backjump_var)
                self.branching_hist[self.curr_level], self.propagate_hist[self.curr_level] = backjump_var, deque()
                update_implication_graph(backjump_var)
        return self.M

if __name__ == "__main__":
    a, b = PropVariable("a"), PropVariable("b")

    c = PropNot(PropAnd(a, b))
    s = SAT(c)
    s.wff_to_CNF()
    s.prepare_solver()
    solver = SATSolver(s.pass_to_sat_clause, s.pass_to_sat_var)
    assignment = solver.solve()
    s.assign_valid(assignment)
    print(s.assign)

    c = PropAnd(a, b)
    s = SAT(c)
    s.wff_to_CNF()
    s.prepare_solver()
    solver = SATSolver(s.pass_to_sat_clause, s.pass_to_sat_var)
    assignment = solver.solve()
    s.assign_valid(assignment)
    print(s.assign)

    c = PropOr(a, b)
    s = SAT(c)
    s.wff_to_CNF()
    s.prepare_solver()
    solver = SATSolver(s.pass_to_sat_clause, s.pass_to_sat_var)
    assignment = solver.solve()
    s.assign_valid(assignment)
    print(s.assign)

    c = PropOr(a, b)
    s = SAT(PropNot(c))
    s.wff_to_CNF()
    s.prepare_solver()
    solver = SATSolver(s.pass_to_sat_clause, s.pass_to_sat_var)
    assignment = solver.solve()
    s.assign_valid(assignment)
    print(s.assign)

    c = PropOr(a, b)
    s = SAT(PropAnd(PropNot(c), c))
    s.wff_to_CNF()
    s.prepare_solver()
    solver = SATSolver(s.pass_to_sat_clause, s.pass_to_sat_var)
    assignment = solver.solve()
    s.assign_valid(assignment)
    print(s.assign)
