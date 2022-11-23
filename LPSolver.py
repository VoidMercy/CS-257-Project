import sys
import scipy
import numpy as np
from ExprNode import *

sys.setrecursionlimit(200000)

class Solver:
	def __init__(self):
		self.conjunction = [] # Conjunction of ExprNodes

	def add(self, expression:ExprNode):
		self.conjunction.append(expression)

	def solve(self):
		# The supported operators here are ADD, SUBTRACT, MULTIPLY, EQUALS, LT, GT, LTE, GTE

		# First, we have to simplify the expression into standard form, which is a tree where all first-level operators are addition or subtraction. To do this, we need to distribute multiplication inwards.
		# this should be a lot easier due to constant simplification, and multiplication rewrite rules

		# step 1. constant simplification. We want to collapse one side of multiplication into a constant
		for i in range(len(self.conjunction)):
			self.conjunction[i] = self.conjunction[i].constant_simplify()

		# step 2. encode linear expression by labeling each node as a new variable
		self.v_idx_map = {} # Maps variable name to v_idx
		self.v_idx = 0
		A_eq = []
		b_eq = []
		A_ub = []
		b_ub = []
		bounds = []
		for expr in self.conjunction:
			print("="*50)
			print(expr)
			A_eq_, b_eq_, A_ub_, b_ub_, bounds_ = self.encode_lp(expr)
			A_eq += A_eq_
			b_eq += b_eq_
			A_ub += A_ub_
			b_ub += b_ub_
			bounds += bounds_
			print(A_eq_)
			print(A_ub_)
			print(b_ub_)
			print(bounds_)
		print("*"*50)
		A_eq_matrix   = np.zeros((len(A_eq), self.v_idx), dtype=np.longlong)
		b_eq_matrix   = np.zeros((len(A_eq)), dtype=np.longlong)
		A_ub_matrix   = np.zeros((len(A_ub), self.v_idx), dtype=np.longlong)
		b_ub_matrix   = np.zeros((len(A_ub)), dtype=np.longlong)
		bounds_matrix = [(None, None)]*self.v_idx
		c_matrix      = np.zeros((self.v_idx), dtype=np.longlong)

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
		for value in self.v_idx_map.values():
			c_matrix[value] = 1

		print(A_eq_matrix)
		print(b_eq_matrix)
		print(A_ub_matrix)
		print(b_ub_matrix)
		print(bounds_matrix)
		print(c_matrix)
		solution = self.solve_ilp(c_matrix, A_ub_matrix, b_ub_matrix, A_eq_matrix, b_eq_matrix, bounds_matrix)
		print()
		print("SOLUTION")
		for v_name, v_idx in self.v_idx_map.items():
			print("{}:{}".format(v_name, solution[v_idx]))

	# Returns (A_eq constraints, b_eq constraints, bounds constraints)
	# A_eq : List[List[Tuple(v_idx, value)]]
	# b_eq : List[value]
	# A_ub : List[List[Tuple(v_idx, value)]]
	# b_ub : List[value]
	# bounds : List[Tuple(v_idx, min, max)]
	def encode_lp(self, expr:ExprNode):
		if isinstance(expr, FunctionNode):
			expr.value = 0
			A_eq, b_eq, A_ub, b_ub, bounds = self.encode_lp(expr.children[0])
			A_eq_2, b_eq_2, A_ub_2, b_ub_2, bounds_2 = self.encode_lp(expr.children[1])
			A_eq += A_eq_2
			b_eq += b_eq_2
			A_ub += A_ub_2
			b_ub += b_ub_2
			bounds += bounds_2

			left, right = expr.children[0], expr.children[1]
			if expr.func_type in set([FunctionEnum.ADD, FunctionEnum.SUBTRACT, FunctionEnum.MULTIPLY]):
				expr.v_idx = self.v_idx
				mod        = self.v_idx + 1
				self.v_idx += 2

				if expr.func_type == FunctionEnum.ADD:
					# left + right == expr + mod * 2^n
					# 0 <= mod <= 1
					# 0 <= expr <= 2^n - 1
					# left + right - expr - 2^n * mod == 0
					A_eq += [[(left.v_idx, 1), (right.v_idx, 1), (expr.v_idx, -1), (mod, -2**expr.width)]]
					b_eq += [0 - left.value - right.value]
					bounds += [(mod, 0, 1), (expr.v_idx, 0, 2**expr.width - 1)]
				elif expr.func_type == FunctionEnum.SUBTRACT:
					# 2^n * mod + left - right = expr
					# 0 <= mod <= 1
					# 0 <= expr <= 2^n - 1
					# 2^n * mod + left - right - expr = 0
					A_eq += [[(left.v_idx, 1), (right.v_idx, -1), (expr.v_idx, -1), (mod, 2**expr.width)]]
					b_eq += [0 - left.value + right.value]
					bounds += [(mod, 0, 1), (expr.v_idx, 0, 2**expr.width - 1)]
				else: # MULTIPLY
					# left * right == expr + mod * 2^n
					# Either left or right is constant
					# 0 <= mod <= 2^n - 1
					# 0 <= expr <= 2^n - 1
					# left * right - expr - 2^n * mod == 0
					if isinstance(right, ConstantNode): 
						left, right = right, left
					A_eq += [[(right.v_idx, left.value), (expr.v_idx, -1), (mod, -2**expr.width)]]
					b_eq += [0]
					bounds += [(mod, 0, 2**expr.width - 1), (expr.v_idx, 0, 2**expr.width - 1)]
				return A_eq, b_eq, A_ub, b_ub, bounds
			else:
				# Equality or comparison
				if expr.func_type == FunctionEnum.EQUALS:
					# A = B
					A_eq += [[(left.v_idx, 1), (right.v_idx, -1)]]
					b_eq += [0 - left.value + right.value]
				elif expr.func_type == FunctionEnum.LE:
					# A <= B
					A_ub += [[(left.v_idx, 1), (right.v_idx, -1)]]
					b_ub += [0 - left.value + right.value]
				elif expr.func_type == FunctionEnum.GE:
					# B <= A
					A_ub += [[(left.v_idx, -1), (right.v_idx, 1)]]
					b_ub += [0 + left.value - right.value]
				return A_eq, b_eq, A_ub, b_ub, bounds
		elif isinstance(expr, ConstantNode):
			expr.v_idx = None
			return [], [], [], [], []
		elif isinstance(expr, VariableNode):
			expr.value = 0
			if expr.name in self.v_idx_map:
				expr.v_idx = self.v_idx_map[expr.name]
				return [], [], [], [], []
			expr.v_idx = self.v_idx
			self.v_idx_map[expr.name] = self.v_idx
			self.v_idx += 1
			return [], [], [], [], [(expr.v_idx, 0, 2**expr.width - 1)]

	# Finds an integer solution to the ILP problem (not necessarily optimal.
	# Bounds are expected to have a min bound of 0. I.e. (0, None), without loss of generality.
	# Returns tuple (x : vector of solutions)
	def solve_ilp(self, c, A_ub, b_ub, A_eq, b_eq, bounds):
		res = scipy.optimize.linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds)
		if not res.success:
			return None
		for i in range(len(res.x)):
			x = res.x[i]
			if np.ceil(x) != x:
				# Branch and bound
				new_bounds = bounds[:]
				new_bounds[i] = (bounds[i][0], np.floor(x))
				res = self.solve_ilp(c, A_ub, b_ub, A_eq, b_eq, new_bounds)
				if res is not None:
					return res
				new_bounds = bounds[:]
				new_bounds[i] = (np.ceil(x), bounds[i][1])
				res = self.solve_ilp(c, A_ub, b_ub, A_eq, b_eq, new_bounds)
				return res
		return [int(i) for i in res.x]

# Let's try solving:
# A + B <= 5
# A + B >= 2

s = Solver()
A = BitVec("A", 32)
B = BitVec("B", 32)
s.add(A + B + BitVecVal(4, 32) - BitVecVal(1, 32) * BitVecVal(3, 32) <= BitVecVal(5, 32))
s.add(A + B >= BitVecVal(2, 32))
s.solve()

