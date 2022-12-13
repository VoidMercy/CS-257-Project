from PropNode import *
from collections import deque

class SAT:
    def __init__(self, wff: PropNode):
        self.wff = wff
        self.constraints = []
        self.match = set()
        self.original_vars = set()
        self.sat_vars = set()
        self.pass_to_sat = set()
        self.assign = dict()
        self.pass_to_sat_var = set()

    # modify self.constraints directly
    def wff_to_CNF(self):
        # generate fresh variable name
        def generate_var(counter: int) -> (PropVariable, int):
            return PropVariable("tseitin_v{}".format(counter)), counter + 1

        # work for each node
        def helper(wff: PropNode, top: PropVariable, counter: int) -> (list, int, bool, PropVariable, bool, PropVariable):
            a = top
            if isinstance(wff.left, PropVariable):
                p, l = wff.left, False
                self.original_vars.add(p)
            else: (p, counter), l = generate_var(counter), True
            if isinstance(wff.right, PropVariable):
                q, r = wff.right, False
                self.original_vars.add(q)
            else: (q, counter), r = generate_var(counter), True
            if wff.op == PropEnum.OR:
                return [[a, PropNot(p)], [a, PropNot(q)], [p, q, PropNot(a)]], counter, l, p, r, q
            elif wff.op == PropEnum.AND:
                return [[a, PropNot(p), PropNot(q)], [p, PropNot(a)], [q, PropNot(a)]], counter, l, p, r, q
            else:
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

    def prepare_solver(self):
        for clause in self.constraints:
            for l in clause:
                if isinstance(l, PropVariable): self.sat_vars.add(l)
                else: self.sat_vars.add(PropNot(l))
        d = dict(zip(list(self.sat_vars), [i+1 for i in range(len(self.sat_vars))]))
        for clause in self.constraints:
            c = set()
            for l in clause:
                if isinstance(l, PropVariable): c.add(d[l])
                else: c.add(-1 * d[PropNot(l)])
            self.pass_to_sat.add(frozenset(c))

        self.pass_to_sat_var = set([i+1 for i in range(len(self.sat_vars))])
        self.match = dict([(v, k) for k, v in d.items() if k in self.original_vars])

    def assign_valid(self, assignment):
        if not assignment: self.assign = None
        for atom, val in assignment.items():
            if atom in self.match.keys():
                self.assign[atom] = val

class SATSolver:
    def __init__(self, delta, vars):
        self.delta = delta
        self.vars = vars
        self.learnts = set()
        self.assigns = dict.fromkeys(list(self.vars), "unassigned")
        self.level = 0
        self.nodes = dict((k, ImplicationNode(k, "unassigned")) for k in list(self.vars))
        self.branching_vars = set()
        self.branching_history = dict()
        self.propagate_history = dict()
        self.branching_count = 0

    def solve(self):
        def update_graph(var, clause=None):
            node = self.nodes[var]
            node.value = self.assigns[var]
            node.level = self.level

            if clause:
                for v in [abs(literal) for literal in clause if abs(literal) != var]:
                    node.parents.append(self.nodes[v])
                    self.nodes[v].children.append(node)
                node.clause = clause

        def unit_propagate():
            def compute_value(literal):
                value = self.assigns[abs(literal)]
                return value if value == "unassigned" else value ^ (literal < 0)

            def compute_clause(clause):
                values = list(map(compute_value, clause))
                return "unassigned" if "unassigned" in values else max(values)

            def is_unit_clause(clause):
                values, unassigned = [], None

                for literal in clause:
                    value = compute_value(literal)
                    values.append(value)
                    unassigned = literal if value == "unassigned" else unassigned

                ret = ((values.count(False) == len(clause) - 1 and values.count("unassigned") == 1) or
                         (len(clause) == 1 and values.count("unassigned") == 1))
                return ret, unassigned

            while True:
                propagate_queue = deque()
                for clause in [x for x in self.delta.union(self.learnts)]:
                    clause_val = compute_clause(clause)
                    if clause_val == True:
                        continue
                    if clause_val == False:
                        return clause
                    else:
                        is_unit, unit_lit = is_unit_clause(clause)
                        if not is_unit: continue
                        prop_pair = (unit_lit, clause)
                        if prop_pair not in propagate_queue:
                            propagate_queue.append(prop_pair)
                if not propagate_queue: return None

                for prop_lit, clause in propagate_queue:
                    prop_var = abs(prop_lit)
                    self.assigns[prop_var] = True if prop_lit > 0 else False
                    update_graph(prop_var, clause=clause)
                    if self.level in self.propagate_history.keys(): self.propagate_history[self.level].append(prop_lit)

        def conflict_analyze(conflict_clause):
            def next_recent_assigned(clause):
                for v in reversed(assign_history):
                    if v in clause or -v in clause:
                        return v, [x for x in clause if abs(x) != abs(v)]

            if self.level == 0: return -1, None

            assign_history = [self.branching_history[self.level]] + list(self.propagate_history[self.level])

            pool_lits = conflict_clause
            done_lits = set()
            curr_level_lits = set()
            prev_level_lits = set()

            while True:
                for lit in pool_lits:
                    if self.nodes[abs(lit)].level == self.level:
                        curr_level_lits.add(lit)
                    else:
                        prev_level_lits.add(lit)

                if len(curr_level_lits) == 1:
                    break

                last_assigned, others = next_recent_assigned(curr_level_lits)

                done_lits.add(abs(last_assigned))
                curr_level_lits = set(others)

                pool_clause = self.nodes[abs(last_assigned)].clause
                pool_lits = [
                    l for l in pool_clause if abs(l) not in done_lits
                ] if pool_clause is not None else []

            learnt = frozenset([l for l in curr_level_lits.union(prev_level_lits)])
            if prev_level_lits:
                level = max([self.nodes[abs(x)].level for x in prev_level_lits])
            else:
                level = self.level - 1

            return level, learnt

        def backtrack(level):
            for var, node in self.nodes.items():
                if node.level <= level:
                    node.children[:] = [child for child in node.children if child.level <= level]
                else:
                    node.value = "unassigned"
                    node.level = -1
                    node.parents = []
                    node.children = []
                    node.clause = None
                    self.assigns[node.variable] = "unassigned"

            self.branching_vars = set([
                var for var in self.vars
                if (self.assigns[var] != "unassigned"
                    and len(self.nodes[var].parents) == 0)
            ])

            levels = list(self.propagate_history.keys())
            for k in levels:
                if k <= level:
                    continue
                del self.branching_history[k]
                del self.propagate_history[k]

        while not (all(var in self.assigns for var in self.vars) and not any(var for var in self.vars if self.assigns[var] == "unassigned")):
            conflict_clause = unit_propagate()
            if conflict_clause is not None:
                # there is conflict in unit propagation
                lvl, learnt = conflict_analyze(conflict_clause)
                if lvl < 0: return False
                self.learnts.add(learnt)
                backtrack(lvl)
                self.level = lvl
            elif (all(var in self.assigns for var in self.vars) and not any(var for var in self.vars if self.assigns[var] == "unassigned")):
                break
            else:
                # branching
                self.level += 1
                self.branching_count += 1
                bt_var, bt_val = next(filter(lambda v: v in self.assigns and self.assigns[v] == "unassigned", self.vars)), True
                self.assigns[bt_var] = bt_val
                self.branching_vars.add(bt_var)
                self.branching_history[self.level], self.propagate_history[self.level] = bt_var, deque()
                update_graph(bt_var)
        return self.assigns

if __name__ == "__main__":
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
    s.prepare_solver()
    solver = SATSolver(s.pass_to_sat, s.pass_to_sat_var)
    assignment = solver.solve()
    s.assign_valid(assignment)
    print(s.assign)

    a, b = PropVariable("a"), PropVariable("b")
    c = PropNot(a)
    s = SAT(c)
    s.wff_to_CNF()
    s.prepare_solver()
    solver = SATSolver(s.pass_to_sat, s.pass_to_sat_var)
    assignment = solver.solve()
    s.assign_valid(assignment)
    print(s.assign)

    c = PropOr(PropVariable("a"), PropVariable("b"))
    s = SAT(c)
    s.wff_to_CNF()
    s.prepare_solver()
    solver = SATSolver(s.pass_to_sat, s.pass_to_sat_var)
    assignment = solver.solve()
    s.assign_valid(assignment)
    print(s.assign)

    c = PropAnd(PropVariable("a"), PropVariable("b"))
    s = SAT(c)
    s.wff_to_CNF()
    s.prepare_solver()
    solver = SATSolver(s.pass_to_sat, s.pass_to_sat_var)
    assignment = solver.solve()
    s.assign_valid(assignment)
    print(s.assign)

    c = PropNot(PropVariable("a"))
    s = SAT(c)
    s.wff_to_CNF()
    s.prepare_solver()
    solver = SATSolver(s.pass_to_sat, s.pass_to_sat_var)
    assignment = solver.solve()
    s.assign_valid(assignment)
    print(s.assign)

    c1 = PropAnd(PropVariable("a"), PropVariable("b"))
    c2 = PropOr(PropVariable("c"), PropVariable("d"))
    c3 = PropNot(PropVariable("e"))
    c4 = PropAnd(c1, c2)
    c5 = PropAnd(c3, c4)
    s = SAT(c5)
    s.wff_to_CNF()
    s.prepare_solver()
    solver = SATSolver(s.pass_to_sat, s.pass_to_sat_var)
    assignment = solver.solve()
    s.assign_valid(assignment)
    print(s.assign)

    c1 = [PropVariable("1")]
    c2 = [PropVariable("1"), PropNot(PropVariable("2"))]
    c3 = [PropVariable("1"), PropNot(PropVariable("3"))]
    c4 = [PropVariable("2"), PropVariable("3"), PropNot(PropVariable("1"))]
    s.wff_to_CNF()
    s.prepare_solver()
    solver = SATSolver(s.pass_to_sat, s.pass_to_sat_var)
    assignment = solver.solve()
    s.assign_valid(assignment)
    print(s.assign)

    c1 = [PropVariable("1")]
    c2 = [PropNot(PropVariable("1")), PropVariable("2")]
    c3 = [PropNot(PropVariable("3")), PropVariable("4")]
    c4 = [PropNot(PropVariable("5")), PropNot(PropVariable("6"))]
    c5 = [PropNot(PropVariable("1")), PropNot(PropVariable("5")), PropVariable("7")]
    c6 = [PropNot(PropVariable("2")), PropNot(PropVariable("5")), PropVariable("6"), PropNot(PropVariable("7"))]
    s.wff_to_CNF()
    s.prepare_solver()
    solver = SATSolver(s.pass_to_sat, s.pass_to_sat_var)
    assignment = solver.solve()
    s.assign_valid(assignment)
    print(s.assign)

    c1 = [PropVariable("1")]
    c2 = [PropNot(PropVariable("1"))]
    s.wff_to_CNF()
    s.prepare_solver()
    solver = SATSolver(s.pass_to_sat, s.pass_to_sat_var)
    assignment = solver.solve()
    s.assign_valid(assignment)
    print(s.assign)

    s, a, b = PropVariable("s"), PropVariable("a"), PropVariable("b")
    c1 = PropAnd(PropAnd(s, PropNot(b)), PropNot(a))
    c2 = PropAnd(PropAnd(PropNot(s), b), PropNot(a))
    c3 = PropAnd(PropAnd(PropNot(s), PropNot(b)), a)
    c4 = PropOr(c1, c2)
    c5 = PropOr(c3, c4)
    s = SAT(c5)
    s.wff_to_CNF()
    s.prepare_solver()
    solver = SATSolver(s.pass_to_sat, s.pass_to_sat_var)
    assignment = solver.solve()
    print(s.match)
    print(assignment)
    print(s.assign)

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
    s.prepare_solver()
    solver = SATSolver(s.pass_to_sat, s.pass_to_sat_var)
    assignment = solver.solve()
    s.assign_valid(assignment)
    print(s.assign)
