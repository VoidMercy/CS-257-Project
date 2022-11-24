import sys
import scipy
import numpy as np
from ExprNode import *
from BitBlaster import Solver as bSolver

sys.setrecursionlimit(200000)

class Solver:
	def __init__(self):
		self.conjunction = [] # Conjunction of ExprNodes
		self.variables = set()
		self.variable_width_map = {}

	def add(self, expression:ExprNode):
		self.conjunction.append(expression)
		self.parse_expression(expression)
	def parse_expression(self, expr:ExprNode):
		if isinstance(expr, VariableNode):
			self.variables.add(expr.name)
			self.variable_width_map[expr.name] = expr.width
		if isinstance(expr, FunctionNode):
			for i in expr.children:
				if isinstance(i, ExprNode):
					self.parse_expression(i)

	def solve(self):
		# The supported operators here are ADD, SUBTRACT, MULTIPLY, EQUALS, LT, GT, LTE, GTE

		# Simplify expression into standard form
		for i in self.conjunction:
			i.equation_skew()
		for i in range(len(self.conjunction)):
			self.conjunction[i] = self.conjunction[i].distribute_constants()
		for i in range(len(self.conjunction)):
			self.conjunction[i] = self.conjunction[i].tree_rotation()
		for i in range(len(self.conjunction)):
			self.conjunction[i] = self.conjunction[i].constant_simplify()
		for i in self.conjunction:
			print(str(i).replace("(", "").replace(")", ""))

		# Now we build the matrix
		v_idx_map = {} # Maps variable name to v_idx
		v_idx = 0

		for v in self.variables:
			v_idx_map[v] = v_idx
			v_idx += 1
		print(v_idx_map)

		# A_eq : List[List[Tuple(v_idx, value)]]
		# b_eq : List[value]
		# A_ub : List[List[Tuple(v_idx, value)]]
		# b_ub : List[value]
		# bounds : List[Tuple(v_idx, min, max)]
		A_eq = []
		b_eq = []
		A_ub = []
		b_ub = []
		bounds = []

		for v in self.variables:
			bounds.append((v_idx_map[v], 0, 2**self.variable_width_map[v] - 1))

		for constraint in self.conjunction:
			A = []
			coeff = (self.find_coefficients(constraint))
			for name, c in coeff.items():
				A.append((v_idx_map[name], c))
			A.append((v_idx, 2**constraint.children[0].width))
			bounds.append((v_idx, 0, 2**constraint.children[0].width - 1))
			v_idx += 1
			b_eq.append(constraint.extract_constant().value)
			A_eq.append(A)

		A_eq_matrix = [[0]*v_idx for i in range(len(A_eq))]
		b_eq_matrix = [0]*len(A_eq)
		A_ub_matrix = [[0]*v_idx for i in range(len(A_eq))]
		b_ub_matrix = [0]*len(A_eq)
		bounds_matrix = [(None, None)]*v_idx
		c_matrix = [0]*v_idx

		for i in range(len(A_eq)):
			for j in A_eq[i]:
				if j[0] is not None:
					A_eq_matrix[i][j[0]] = j[1]
			b_eq_matrix[i] = b_eq[i]
		for i in range(len(A_ub)):
			for j in A_ub[i]:
				if j[0] is not None:
					A_ub_matrix[i][j[0]] = j[1]
			b_ub_matrix[i] = b_ub[i]
		for i in bounds:
			bounds_matrix[i[0]] = (i[1], i[2])
		# for i in range(len(self.variables), v_idx):
		# 	c_matrix[i] = 1
		for i in range(len(self.variables)):
			c_matrix[i] = 1

		print(A_eq_matrix)
		print(b_eq_matrix)
		print(A_ub_matrix)
		print(b_ub_matrix)
		print(bounds_matrix)
		print(c_matrix)
		solution = self.solve_ilp(c_matrix, A_ub_matrix, b_ub_matrix, A_eq_matrix, b_eq_matrix, bounds_matrix)
		print()
		print("SOLUTION")
		ret = {}
		if solution is not None:
			for v_name, v_idx in v_idx_map.items():
				print("{}:{}".format(v_name, solution[v_idx]))
				ret[v_name] = solution[v_idx]
		else:
			print("UNSAT")
		return ret

	def find_coefficients(self, expr:ExprNode):
		if isinstance(expr, FunctionNode):
			if expr.func_type == FunctionEnum.MULTIPLY:
				return {expr.children[0].name : expr.children[1].value}
			elif expr.func_type == FunctionEnum.SUBTRACT:
				left = self.find_coefficients(expr.children[0])
				right = self.find_coefficients(expr.children[1])
				for key, value in right.items():
					if key not in left:
						left[key] = 0
					left[key] -= value
				return left
			else:
				left = self.find_coefficients(expr.children[0])
				right = self.find_coefficients(expr.children[1])
				for key, value in right.items():
					if key not in left:
						left[key] = 0
					left[key] += value
				return left
		elif isinstance(expr, VariableNode):
			return {expr.name : 1}
		elif isinstance(expr, ConstantNode):
			return {}
	# Finds an integer solution to the ILP problem (not necessarily optimal.
	# Bounds are expected to have a min bound of 0. I.e. (0, None), without loss of generality.
	# Returns tuple (x : vector of solutions)
	def solve_ilp(self, c, A_ub, b_ub, A_eq, b_eq, bounds):
		queue = []
		queue.append(bounds)
		while len(queue) != 0:
			cur_bounds = queue.pop(0)
			res = scipy.optimize.linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=cur_bounds)
			if not res.success:
				continue
			print("BOUNDS", cur_bounds, res.x)
			success = True
			for i in range(len(res.x)):
				x = res.x[i]
				if abs(x - round(x)) > 0.000000000001:
					print("L", x, np.ceil(x))
					# Branch and bound
					new_bounds = cur_bounds[:]
					new_bounds[i] = (cur_bounds[i][0], np.floor(x))
					queue.append(new_bounds)
					new_bounds = cur_bounds[:]
					new_bounds[i] = (np.ceil(x), cur_bounds[i][1])
					queue.append(new_bounds)
					success = False
			if success:
				print("WIN")
				return [round(i) for i in res.x]

# Let's try solving:
# A + B <= 5
# A + B >= 2

# s = Solver()
# A = BitVec("A", 32)
# B = BitVec("B", 32)
# C = BitVec("C", 32)
# D = BitVec("D", 32)
# E = BitVec("E", 32)
# F = BitVec("F", 32)
# G = BitVec("G", 32)
# H = BitVec("H", 32)

# s.add(((A - 2) - BitVecVal(6, 32) * (C - D)) - ((BitVecVal(5, 32) * (F + 5 * 2)) - (BitVecVal(8, 32) - H)) == BitVecVal(5, 32) - B * 4 + C * 5)

# s.solve()

s = Solver()
s2 = bSolver()

N = 4
MAX = 1000
BITS = 32

array = np.random.randint(0, MAX, size=(N, N))
x = np.random.randint(0, MAX, size=(N, 1))
b = array @ x

variables = [BitVec("A" + str(i), BITS) for i in range(N)]
for row in range(N):
	expression = []
	for col in range(N):
		expression.append(BitVecVal(int(array[row][col]), BITS) * variables[col])
	expression = reduce(lambda x,y:x + y, expression)
	s.add(expression == BitVecVal(int(b[row]), BITS))
	s2.add(expression == BitVecVal(int(b[row]), BITS))

ret = s.solve()


print(ret)

x_solve = np.zeros((N, 1), dtype=np.longlong)
for i in range(N):
	x_solve[i] = ret["A" + str(i)]
print(b)
print(array @ x_solve)

# ret = s2.solve()
# print(ret)