import sys
import scipy
import numpy as np
from ExprNode import *
from BitBlaster import Solver as bSolver
import zlib

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

		# A : List[List[Tuple(v_idx, value)]]
		# b_u : List[value]
		# b_l : List[value]
		# bounds : List[Tuple(v_idx, min, max)]
		A   = []
		b_u = []
		b_l = []
		bounds = []

		for v in self.variables:
			bounds.append((v_idx_map[v], 0, 2**self.variable_width_map[v] - 1))

		for constraint in self.conjunction:
			A_temp = []
			coeff = (self.find_coefficients(constraint))
			for name, c in coeff.items():
				A_temp.append((v_idx_map[name], c))
			A_temp.append((v_idx, -2**constraint.children[0].width))
			b_u.append(constraint.extract_constant().value)
			b_l.append(b_u[-1])
			A.append(A_temp)
			v_idx += 2

		A_matrix = [[0]*v_idx for i in range(len(A))]
		b_u_matrix = [0]*len(A)
		b_l_matrix = [0]*len(A)
		bounds_matrix = [(None, None)]*v_idx
		c_matrix = [0]*v_idx

		for i in range(len(A)):
			for j in A[i]:
				if j[0] is not None:
					A_matrix[i][j[0]] = j[1]
			b_u_matrix[i] = b_u[i]
			b_l_matrix[i] = b_l[i]
		for i in bounds:
			bounds_matrix[i[0]] = (i[1], i[2])
		for value in v_idx_map.values():
			c_matrix[value] = 1

		print(A_matrix)
		print(b_u_matrix)
		print(b_l_matrix)
		print(bounds_matrix)
		print(c_matrix)
		solution = self.solve_ilp(c_matrix, A_matrix, b_u_matrix, b_l_matrix, bounds_matrix)
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
	def solve_ilp(self, c_matrix, A_matrix, b_u_matrix, b_l_matrix, bounds_matrix):
		constraints = scipy.optimize.LinearConstraint(A_matrix, b_l_matrix, b_u_matrix)
		integrality = np.ones_like(c_matrix)
		bounds = scipy.optimize.Bounds(lb=[i[0] for i in bounds_matrix], ub=[i[1] for i in bounds_matrix])
		print("Start solving")
		# solution = scipy.optimize.milp(c=c_matrix, constraints=constraints, integrality=integrality, bounds=bounds, options={"time_limit":1})
		solution = scipy.optimize.milp(c=c_matrix, constraints=constraints, integrality=integrality)
		print(constraints)
		print(integrality)
		print(bounds)
		print(solution)
		if not solution.success:
			return None
		return [round(i) for i in solution.x]

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

# s = Solver()
# s2 = bSolver()

# N = 4
# MAX = 2**10
# BITS = 32

# array = np.random.randint(0, MAX, size=(N, N))
# while np.linalg.matrix_rank(array) != N:
# 	array = np.random.randint(0, MAX, size=(N, N))
# x = np.random.randint(0, MAX, size=(N, 1))
# b = array @ x
# for i in b:
# 	assert i < 2**BITS

# print("ARRAY", array)
# print("X", x)
# print("B", b)

# variables = [BitVec("A" + str(i), BITS) for i in range(N)]
# for row in range(N):
# 	expression = []
# 	for col in range(N):
# 		expression.append(BitVecVal(int(array[row][col]), BITS) * variables[col])
# 	expression = reduce(lambda x,y:x + y, expression)
# 	print(expression)
# 	s.add(expression == BitVecVal(int(b[row]), BITS))
# 	s2.add(expression == BitVecVal(int(b[row]), BITS))

# print("CONJUNCTIONS")
# for i in s.conjunction:
# 	print(i)

# ret = s.solve()

# print(ret)

# x_solve = np.zeros((N, 1), dtype=np.longlong)
# for i in range(N):
# 	x_solve[i] = ret["A" + str(i)]
# assert(all(b == array @ x_solve))

# ret = s2.solve()
# print(ret)

A = BitVec("A", 28)
s = Solver()
s.add(A * 123124124 == 231974516)
print(s.solve())
