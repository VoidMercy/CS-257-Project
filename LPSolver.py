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
		# for i in self.conjunction:
		# 	i.equation_skew()
		# for i in range(len(self.conjunction)):
		# 	self.conjunction[i] = self.conjunction[i].distribute_constants()
		# for i in range(len(self.conjunction)):
		# 	self.conjunction[i] = self.conjunction[i].tree_rotation()
		for i in range(len(self.conjunction)):
			self.conjunction[i] = self.conjunction[i].constant_simplify()
		for i in range(len(self.conjunction)):
			print(self.conjunction[i])

		# step 2. encode linear expression by labeling each node as a new variable
		self.v_idx_map = {} # Maps variable name to v_idx
		self.v_idx = 0
		A = []
		b_u = []
		b_l = []
		bounds = []
		for expr in self.conjunction:
			print("="*50)
			print(expr)
			A_, b_u_, b_l_, bounds_ = self.encode_lp(expr)
			A += A_
			b_u += b_u_
			b_l += b_l_
			bounds += bounds_
		print("*"*50)
		print(A)
		print(self.v_idx)
		A_matrix = [[0]*self.v_idx for i in range(len(A))]
		b_u_matrix = [0]*len(A)
		b_l_matrix = [0]*len(A)
		bounds_matrix = [(0, np.inf)]*self.v_idx
		c_matrix      = np.zeros((self.v_idx), dtype=np.longlong)

		for i in range(len(A)):
			for j in A[i]:
				if j[0] is not None:
					A_matrix[i][j[0]] = j[1]
			b_u_matrix[i] = b_u[i]
			b_l_matrix[i] = b_l[i]
		for i in bounds:
			bounds_matrix[i[0]] = (i[1], i[2])
		# for i in range(self.v_idx):
		# 	if i not in self.v_idx_map.values():
		# 		c_matrix[i] = 1
		for value in self.v_idx_map.values():
			c_matrix[value] = 1

		solution = self.solve_milp(c_matrix, A_matrix, b_u_matrix, b_l_matrix, bounds_matrix)
		print()
		print("SOLUTION")
		ret = {}
		if solution is not None:
			for v_name, v_idx in self.v_idx_map.items():
				ret[v_name] = solution[v_idx]
		else:
			print("UNSAT")
		return ret

	# Returns (A_eq constraints, b_eq constraints, bounds constraints)
	# A : List[List[Tuple(v_idx, value)]]
	# b_u : List[value]
	# b_l : List[value]
	# bounds : List[Tuple(v_idx, min, max)]
	def encode_lp(self, expr:ExprNode, do_mod=False):
		if isinstance(expr, FunctionNode):
			expr.value = 0
			A, b_u, b_l, bounds = self.encode_lp(expr.children[0])

			left = expr.children[0]
			if expr.func_type in two_operand_mapping:
				A_2, b_u_2, b_l_2, bounds_2 = self.encode_lp(expr.children[1])
				A += A_2
				b_u += b_u_2
				b_l += b_l_2
				bounds += bounds_2
				right = expr.children[1]
			if expr.func_type in set([FunctionEnum.ADD, FunctionEnum.SUBTRACT, FunctionEnum.MULTIPLY, FunctionEnum.BITWISE_AND, FunctionEnum.BITWISE_OR, FunctionEnum.BITWISE_NOT]):
				if expr.func_type in set([FunctionEnum.ADD, FunctionEnum.SUBTRACT, FunctionEnum.MULTIPLY]):
					expr.v_idx = self.v_idx
					if do_mod:
						mod        = self.v_idx + 1
						self.v_idx += 2
					else:
						self.v_idx += 1

				if expr.func_type == FunctionEnum.ADD:
					# left + right == expr + mod * 2^n
					# 0 <= mod <= 1
					# 0 <= expr <= 2^n - 1
					# left + right - expr - 2^n * mod == 0
					if do_mod:
						A += [[(left.v_idx, 1), (right.v_idx, 1), (expr.v_idx, -1), (mod, -2**expr.width)]]
						bounds += [(mod, 0, 1), (expr.v_idx, 0, 2**expr.width - 1)]
					else:
						A += [[(left.v_idx, 1), (right.v_idx, 1), (expr.v_idx, -1)]]
						bounds += [(expr.v_idx, 0, 2**expr.width - 1)]
					b_l += [0 - left.value - right.value]
					b_u += [0 - left.value - right.value]
				elif expr.func_type == FunctionEnum.SUBTRACT:
					expr.v_idx = self.v_idx
					# 2^n * mod + left - right = expr
					# 0 <= mod <= 1
					# 0 <= expr <= 2^n - 1
					# 2^n * mod + left - right - expr = 0
					if do_mod:
						A += [[(left.v_idx, 1), (right.v_idx, -1), (expr.v_idx, -1), (mod, 2**expr.width)]]
						bounds += [(mod, 0, 1), (expr.v_idx, 0, 2**expr.width - 1)]
					else:
						A += [[(left.v_idx, 1), (right.v_idx, -1), (expr.v_idx, -1)]]
						bounds += [(expr.v_idx, 0, 2**expr.width - 1)]
					b_l += [0 - left.value + right.value]
					b_u += [0 - left.value + right.value]
				elif expr.func_type == FunctionEnum.MULTIPLY: # MULTIPLY
					expr.v_idx = self.v_idx
					# left * right == expr + mod * 2^n
					# Either left or right is constant
					# 0 <= mod <= 2^n - 1
					# 0 <= expr <= 2^n - 1
					# left * right - expr - 2^n * mod == 0
					if isinstance(right, ConstantNode): 
						left, right = right, left
					if do_mod:
						A += [[(right.v_idx, left.value), (expr.v_idx, -1), (mod, -2**expr.width)]]
						bounds += [(mod, 0, 2**expr.width - 1), (expr.v_idx, 0, 2**expr.width - 1)]
					else:
						A += [[(right.v_idx, left.value), (expr.v_idx, -1)]]
						bounds += [(expr.v_idx, 0, 2**expr.width - 1)]
					b_l += [0]
					b_u += [0]
				elif expr.func_type == FunctionEnum.BITWISE_AND:
					# Expand both left and right into bits
					constraint = [(left.v_idx, 1)]
					left_bits_v_idx = []
					for i in range(expr.width):
						# left == (v_idx) * 2^0 + (v_idx_1) * 2^1 + (v_idx_2) * 2^2 ...
						constraint.append((self.v_idx, -2**i))
						left_bits_v_idx.append(self.v_idx)
						bounds.append((self.v_idx, 0, 1))
						self.v_idx += 1
					A.append(constraint)
					b_l.append(0)
					b_u.append(0)
					constraint = [(right.v_idx, 1)]
					right_bits_v_idx = []
					for i in range(expr.width):
						# left == (v_idx) * 2^0 + (v_idx_1) * 2^1 + (v_idx_2) * 2^2 ...
						constraint.append((self.v_idx, -2**i))
						right_bits_v_idx.append(self.v_idx)
						bounds.append((self.v_idx, 0, 1))
						self.v_idx += 1
					A.append(constraint)
					b_l.append(0)
					b_u.append(0)

					z_bits_v_idx = []
					for i in range(expr.width):
						# Z[0] <= left[0]
						# Z[0] <= right[0]
						# Z[0] >= left[0] + right[0] - 1
						# Z[0] - left[0] - right[0] >= -1
						A.append([(self.v_idx, 1), (left_bits_v_idx[i], -1)])
						b_l.append(-1)
						b_u.append(0)
						A.append([(self.v_idx, 1), (right_bits_v_idx[i], -1)])
						b_l.append(-1)
						b_u.append(0)
						A.append([(self.v_idx, 1), (left_bits_v_idx[i], -1), (right_bits_v_idx[i], -1)])
						b_l.append(-1)
						b_u.append(1)
						bounds.append((self.v_idx, 0, 1))
						z_bits_v_idx.append(self.v_idx)
						self.v_idx += 1
					# Combine Z into word variable

					expr.v_idx = self.v_idx
					constraint = [(expr.v_idx, 1)]
					self.v_idx += 1
					for i in range(expr.width):
						# Z = z[0] * 2^0 + z[1] * 2^1 + ...
						constraint.append((z_bits_v_idx[i], -2**i))
					A.append(constraint)
					b_l.append(0)
					b_u.append(0)
					bounds.append((expr.v_idx, 0, 2**expr.width - 1))
				elif expr.func_type == FunctionEnum.BITWISE_OR:
					# Expand both left and right into bits
					constraint = [(left.v_idx, 1)]
					left_bits_v_idx = []
					for i in range(expr.width):
						# left == (v_idx) * 2^0 + (v_idx_1) * 2^1 + (v_idx_2) * 2^2 ...
						constraint.append((self.v_idx, -2**i))
						left_bits_v_idx.append(self.v_idx)
						bounds.append((self.v_idx, 0, 1))
						self.v_idx += 1
					A.append(constraint)
					b_l.append(0)
					b_u.append(0)
					constraint = [(right.v_idx, 1)]
					right_bits_v_idx = []
					for i in range(expr.width):
						# left == (v_idx) * 2^0 + (v_idx_1) * 2^1 + (v_idx_2) * 2^2 ...
						constraint.append((self.v_idx, -2**i))
						right_bits_v_idx.append(self.v_idx)
						bounds.append((self.v_idx, 0, 1))
						self.v_idx += 1
					A.append(constraint)
					b_l.append(0)
					b_u.append(0)

					z_bits_v_idx = []
					for i in range(expr.width):
						# Z[0] >= left[0]
						# Z[0] >= right[0]
						# Z[0] <= left[0] + right[0]
						# Z[0] <= 1
						A.append([(self.v_idx, 1), (left_bits_v_idx[i], -1)])
						b_l.append(0)
						b_u.append(1)
						A.append([(self.v_idx, 1), (right_bits_v_idx[i], -1)])
						b_l.append(0)
						b_u.append(1)
						A.append([(self.v_idx, 1), (left_bits_v_idx[i], -1), (right_bits_v_idx[i], -1)])
						b_l.append(-1)
						b_u.append(0)
						bounds.append((self.v_idx, 0, 1))
						z_bits_v_idx.append(self.v_idx)
						self.v_idx += 1
					# Combine Z into word variable

					expr.v_idx = self.v_idx
					constraint = [(expr.v_idx, 1)]
					self.v_idx += 1
					for i in range(expr.width):
						# Z = z[0] * 2^0 + z[1] * 2^1 + ...
						constraint.append((z_bits_v_idx[i], -2**i))
					A.append(constraint)
					b_l.append(0)
					b_u.append(0)
					bounds.append((expr.v_idx, 0, 2**expr.width - 1))
				elif expr.func_type == FunctionEnum.BITWISE_NOT:
					# Expand both left and right into bits
					constraint = [(left.v_idx, 1)]
					left_bits_v_idx = []
					for i in range(expr.width):
						# left == (v_idx) * 2^0 + (v_idx_1) * 2^1 + (v_idx_2) * 2^2 ...
						constraint.append((self.v_idx, -2**i))
						left_bits_v_idx.append(self.v_idx)
						bounds.append((self.v_idx, 0, 1))
						self.v_idx += 1
					A.append(constraint)
					b_l.append(0)
					b_u.append(0)

					z_bits_v_idx = []
					for i in range(expr.width):
						# Z[0] = 1 - left[0]
						A.append([(self.v_idx, 1), (left_bits_v_idx[i], 1)])
						b_l.append(1)
						b_u.append(1)
						bounds.append((self.v_idx, 0, 1))
						z_bits_v_idx.append(self.v_idx)
						self.v_idx += 1
					# Combine Z into word variable
					expr.v_idx = self.v_idx
					constraint = [(expr.v_idx, 1)]
					self.v_idx += 1
					for i in range(expr.width):
						# Z = z[0] * 2^0 + z[1] * 2^1 + ...
						constraint.append((z_bits_v_idx[i], -2**i))
					A.append(constraint)
					b_l.append(0)
					b_u.append(0)
					bounds.append((expr.v_idx, 0, 2**expr.width - 1))

				return A, b_u, b_l, bounds
			else:
				# Equality or comparison
				if expr.func_type == FunctionEnum.EQUALS:
					# A = B
					A += [[(left.v_idx, 1), (right.v_idx, -1)]]
					b_l += [0 - left.value + right.value]
					b_u += [0 - left.value + right.value]
				elif expr.func_type == FunctionEnum.LE:
					# A <= B
					A += [[(left.v_idx, 1), (right.v_idx, -1)]]
					b_l += [-np.inf]
					b_u += [0 - left.value + right.value]
				elif expr.func_type == FunctionEnum.GE:
					# B <= A
					A += [[(left.v_idx, -1), (right.v_idx, 1)]]
					b_l += [0 + left.value - right.value]
					b_u += [np.inf]
				return A, b_u, b_l, bounds
		elif isinstance(expr, ConstantNode):
			expr.v_idx = None
			return [], [], [], []
		elif isinstance(expr, VariableNode):
			expr.value = 0
			if expr.name in self.v_idx_map:
				expr.v_idx = self.v_idx_map[expr.name]
				return [], [], [], []
			expr.v_idx = self.v_idx
			self.v_idx_map[expr.name] = self.v_idx
			self.v_idx += 1
			return [], [], [], [(expr.v_idx, 0, 2**expr.width - 1)]

	def solve_milp(self, c_matrix, A_matrix, b_u_matrix, b_l_matrix, bounds_matrix):
		print("A", A_matrix)
		print("B_L", b_l_matrix)
		print("B_U", b_u_matrix)
		constraints = scipy.optimize.LinearConstraint(A_matrix, b_l_matrix, b_u_matrix)
		integrality = np.ones_like(c_matrix)
		bounds = scipy.optimize.Bounds(lb=[i[0] for i in bounds_matrix], ub=[i[1] for i in bounds_matrix])
		print("BOUNDS", bounds)
		# exit()
		print("Start solving")
		solution = scipy.optimize.milp(c=c_matrix, constraints=constraints, integrality=integrality, bounds=bounds)
		# solution = scipy.optimize.milp(c=c_matrix, constraints=constraints, integrality=integrality)
		print(solution)
		if not solution.success:
			return None
		return [round(i) for i in solution.x]

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
C = BitVec("C", 32)
s.add(~A == 7)
# s.add(A + 2 == 3)
# s.add((A + BitVecVal(5, 32) * (B + 3)) & C == 1337)
print(s.solve())
exit()

s = Solver()

N = 2
MAX = 2000
BITS = 32

array = np.random.randint(0, MAX, size=(N, N))
x = np.random.randint(0, MAX, size=(N, 1))
print("X", x)
b = array @ x
for i in b:
	assert i < 2**(BITS)

variables = [BitVec("A" + str(i), BITS) for i in range(N)]
for row in range(N):
	expression = []
	for col in range(N):
		expression.append(BitVecVal(int(array[row][col]), BITS) * variables[col])
	expression = reduce(lambda x,y:x + y, expression)
	s.add(expression == BitVecVal(int(b[row]), BITS))

ret = s.solve()

print("RET", ret)

x_solve = np.zeros((N, 1), dtype=np.longlong)
for i in range(N):
	x_solve[i] = ret["A" + str(i)]
assert(all(b == array @ x_solve))

