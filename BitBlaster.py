import z3
import sys
import math
from ExprNode import *
from PropNode import *
from typing import List, Tuple
from functools import reduce
from SATSolver import *

sys.setrecursionlimit(200000)

class Solver:
	def __init__(self):
		self.conjunction = [] # Conjunction of ExprNodes
		self.theory_prop_map : dict[VariableNode, List[PropVariable]] = {}

	def add(self, expression:ExprNode):
		self.conjunction.append(expression)

	def solve(self, solver = 0):
		expression = reduce(lambda x,y: And(x, y), self.conjunction)
		prop_vars, equation, variables = self.BitBlast(expression)
		assert len(prop_vars) == 1
		equation = PropAnd(equation, prop_vars[0])
		# print("Expression", expression)
		# print(equation)
		# print(self.theory_prop_map)

		# SAT solve with z3
		if solver == 0:
			model = self.z3_solve(variables, equation)
			if model is None:
				return False
			else:
				return model
		else:
			model = self.sat_solve(variables, equation)
			if model is None:
				return False
			else: return model

	def BitBlast(self, node:ExprNode, v_idx=0) -> Tuple[List[PropNode], PropNode, List[str]]:
		if isinstance(node, ConstantNode):
			return [PropConstant(int(i)) for i in bin(node.value)[2:].zfill(node.width)], PropConstant(1), []

		elif isinstance(node, VariableNode):
			if node in self.theory_prop_map:
				return self.theory_prop_map[node], PropConstant(1), self.theory_prop_map[node]
			new_variables = [PropVariable("v{}".format(i + v_idx)) for i in range(node.width)]
			self.theory_prop_map[node] = new_variables
			return new_variables, PropConstant(1), new_variables

		else:
			left_vector, left_equation, left_variables    = self.BitBlast(node.children[0], v_idx)
			if node.func_type in two_operand_mapping:
				right_vector, right_equation, right_variables = self.BitBlast(node.children[1], v_idx + len(left_variables))
				variables                                     = left_variables + right_variables
				equation                                      = PropAnd(left_equation, right_equation)
			else:
				variables                                     = left_variables
				equation                                      = left_equation

			if node.func_type == FunctionEnum.EQUALS:
				eq_var = PropVariable("v{}".format(v_idx + len(variables)))
				eq_equation = PropConstant(1)
				for i in range(node.children[0].width):
					eq_equation = PropAnd(eq_equation, PropIff(left_vector[i], right_vector[i]))
				equation = PropAnd(equation, PropIff(eq_var, eq_equation))
				return [eq_var], equation, variables + [eq_var]

			elif node.func_type == FunctionEnum.BITWISE_AND or node.func_type == FunctionEnum.AND:
				new_variables = [PropVariable("v{}".format(i + v_idx + len(variables))) for i in range(node.width)]
				for i in range(node.children[0].width):
					equation = PropAnd(equation, PropIff(new_variables[i], PropAnd(left_vector[i], right_vector[i])))
				return new_variables, equation, variables + new_variables

			elif node.func_type == FunctionEnum.BITWISE_OR or node.func_type == FunctionEnum.OR:
				new_variables = [PropVariable("v{}".format(i + v_idx + len(variables))) for i in range(node.width)]
				for i in range(node.children[0].width):
					equation = PropAnd(equation, PropIff(new_variables[i], PropOr(left_vector[i], right_vector[i])))
				return new_variables, equation, variables + new_variables

			elif node.func_type == FunctionEnum.BITWISE_XOR:
				new_variables = [PropVariable("v{}".format(i + v_idx + len(variables))) for i in range(node.width)]
				for i in range(node.children[0].width):
					equation = PropAnd(equation, PropIff(new_variables[i], PropXor(left_vector[i], right_vector[i])))
				return new_variables, equation, variables + new_variables

			elif node.func_type == FunctionEnum.BITWISE_NOT or node.func_type == FunctionEnum.NOT:
				new_variables = [PropVariable("v{}".format(i + v_idx + len(variables))) for i in range(node.width)]
				for i in range(node.children[0].width):
					equation = PropAnd(equation, PropIff(new_variables[i], PropNot(left_vector[i])))
				return new_variables, equation, variables + new_variables

			elif node.func_type == FunctionEnum.EXTRACT:
				return left_vector[len(left_vector)-node.children[1]-1:len(left_vector)-node.children[2]], equation, variables

			elif node.func_type == FunctionEnum.CONCAT:
				return left_vector + right_vector, equation, variables

			elif node.func_type == FunctionEnum.ADD:
				new_variables = [PropVariable("v{}".format(i + v_idx + len(variables))) for i in range(node.width)]
				carries       = [PropConstant(0)] + [PropVariable("v{}".format(i + v_idx + len(variables) + node.width)) for i in range(node.width)]
				left_vector, right_vector = left_vector[::-1], right_vector[::-1]
				for i in range(node.children[0].width):
					s, cout = PropFullAdder(left_vector[i], right_vector[i], carries[i])
					equation = PropAnd(equation, PropAnd(PropIff(new_variables[i], s), PropIff(carries[i + 1], cout)))
				return new_variables[::-1], equation, variables + new_variables + carries[1:]

			elif node.func_type == FunctionEnum.SUBTRACT:
				return self.BitBlast(node.children[0] + (~node.children[1] + BitVecVal(1, node.children[1].width)))

			elif node.func_type == FunctionEnum.LSHIFT or node.func_type == FunctionEnum.RSHIFT:
				rounds = math.ceil(math.log2(node.width))
				right_vector = right_vector[::-1]
				if node.func_type == FunctionEnum.LSHIFT:
					left_vector = left_vector[::-1]
				current_vector = left_vector
				for r in range(rounds):
					round_vector = [PropVariable("v{}".format(i + v_idx + len(variables))) for i in range(node.width)]
					variables += round_vector
					for z in range(2**r):
						equation = PropAnd(equation, PropIff(round_vector[z], PropAnd(PropNot(right_vector[r]), current_vector[z])))
					for z in range(2**r, node.width):
						equation = PropAnd(equation, PropIff(round_vector[z], PropMux(right_vector[r], current_vector[z - 2**r], current_vector[z])))
					current_vector = round_vector
				if node.func_type == FunctionEnum.LSHIFT:
					current_vector = current_vector[::-1]
				return current_vector, equation, variables

			elif node.func_type == FunctionEnum.MULTIPLY:
				left_vector, right_vector = left_vector[::-1], right_vector[::-1]
				partial_products = []
				for i in range(node.width):
					partial_products.append([PropConstant(0) for _ in range(i)] + [PropAnd(j, right_vector[i]) for j in left_vector[:node.width - i]])
				while len(partial_products) > 1:
					a, b = partial_products.pop(), partial_products.pop()
					new_sum = [PropVariable("v{}".format(i + v_idx + len(variables))) for i in range(node.width)]
					carries = [PropConstant(0)] + [PropVariable("v{}".format(i + v_idx + len(variables) + node.width)) for i in range(node.width)]
					variables += new_sum + carries[1:]
					for i in range(node.width):
						s, cout = PropFullAdder(a[i], b[i], carries[i])
						equation = PropAnd(equation, PropAnd(PropIff(new_sum[i], s), PropIff(carries[i + 1], cout)))
					partial_products = [new_sum] + partial_products
				return partial_products[0][::-1], equation, variables

			elif node.func_type == FunctionEnum.LT:
				r = [PropVariable("v{}".format(i + v_idx + len(variables))) for i in range(node.children[0].width)] + [PropConstant(0)]
				for i in range(node.children[0].width):
					equation = PropAnd(equation, PropIff(r[i], PropOr(PropAnd(PropNot(left_vector[i]), right_vector[i]), PropAnd(r[i + 1], PropOr(PropNot(left_vector[i]), right_vector[i])))))
				return [r[0]], equation, variables + r[:-1]

			elif node.func_type == FunctionEnum.GT:
				return self.BitBlast(node.children[1] < node.children[0], v_idx)

			elif node.func_type == FunctionEnum.LE:
				return self.BitBlast(Or(node.children[0] < node.children[1], node.children[0] == node.children[1]), v_idx)

			elif node.func_type == FunctionEnum.GE:
				return self.BitBlast(Or(node.children[1] < node.children[0], node.children[0] == node.children[1]), v_idx)

		raise Exception("Unsupported OP", node.func_type)

	def z3_solve(self, variables:List[str], wff:PropNode):
		z3_mapping = {v.name: z3.Bool(v.name) for v in variables} # Name to z3 Bool mapping
		constraint = wff.convert_z3(z3_mapping)
		s = z3.Solver()
		s.add(constraint)
		if s.check() == z3.sat:
			m = s.model()

			model : dict[VariableNode, ConstantNode] = {}
			for variable_node, prop_variables in self.theory_prop_map.items():
				concrete_bits = [m[z3_mapping[i.name]] for i in prop_variables]
				value = 0
				for b in concrete_bits:
					value = value << 1
					if z3.is_true(b):
						value = value | 1
				model[variable_node] = ConstantNode(value, variable_node.width)
			return model
		else:
			return None

	def sat_solve(self, variables:List[str], wff:PropNode):
		s = SAT(wff)
		s.wff_to_CNF()
		solver = SATSolver(s.constraints)
		res = solver.solve()
		if res:
			model : dict[VariableNode, ConstantNode] = {}
			for variable_node, prop_variables in self.theory_prop_map.items():
				concrete_bits = [res[i.name] if i.name in res.keys() else True for i in prop_variables]
				value = 0
				for b in concrete_bits:
					value = value << 1
					if b: value |= 1
				model [variable_node] = ConstantNode(value, variable_node.width)
			return model
		return None

if __name__ == "__main__":
	a = BitVec("A", 5)
	b = BitVec("B", 5)
	c = BitVec("C", 5)
	s = Solver()

	s.add(BitVecVal(5, 5) & a == BitVecVal(1, 5))
	model = s.solve()
	print("z3, Model:", model, "\n")
	model = s.solve(1)
	print("sat, Model:", model, "\n")

	s = Solver()
	s.add(BitVecVal(0, 5) | a == BitVecVal(3, 5))
	model = s.solve()
	print("z3, Model:", model, "\n")
	model = s.solve(1)
	print("sat, Model:", model, "\n")

	s = Solver()
	s.add(BitVecVal(5, 5) ^ a == BitVecVal(3, 5))
	model = s.solve()
	print("Model:", model, "\n")

	s = Solver()
	s.add(~a == BitVecVal(3, 5))
	model = s.solve()
	print("Model:", model, "\n")

	s = Solver()
	left = a & BitVecVal(0b11110, 5) == BitVecVal(0b10100, 5)
	right = a & BitVecVal(0b00001, 5) == BitVecVal(0b00001, 5)
	s.add(And(left, right))
	model = s.solve()
	print("Model:", model, "\n")

	s = Solver()
	left = a & BitVecVal(0b11110, 5) == BitVecVal(0b10100, 5)
	right = a & BitVecVal(0b00001, 5) == BitVecVal(0b00001, 5)
	s.add(And(left, right))
	model = s.solve()
	print("Model:", model, "\n")

	s = Solver()
	left = a & BitVecVal(0b11110, 5) == BitVecVal(0b10100, 5)
	right = a & BitVecVal(0b11111, 5) == BitVecVal(0b01101, 5)
	s.add(Or(left, right))
	model = s.solve()
	print("Model:", model, "\n")

	s = Solver()
	left = a & BitVecVal(0b11111, 5) == BitVecVal(0b00000, 5)
	s.add(Not(left))
	model = s.solve()
	print("Model:", model, "\n")

	s = Solver()
	left = Extract(a, 2, 0) == BitVecVal(0b101, 3)
	right = Extract(a, 4, 3) == BitVecVal(0b01, 2)
	s.add(And(left, right))
	model = s.solve()
	print("Model:", model, "\n")

	s = Solver()
	s.add(Concat(a, b) == BitVecVal(0b1100110010, 10))
	model = s.solve()
	print("Model:", model, "\n")

	s = Solver()
	s.add(a + b == BitVecVal(0b00010, 5))
	s.add(a == BitVecVal(0b00001, 5))
	model = s.solve()
	print("Model:", model, "\n")

	s = Solver()
	s.add(a - b == BitVecVal(0b00010, 5))
	s.add(b == BitVecVal(0b00001, 5))
	model = s.solve()
	print("Model:", model, "\n")

	s = Solver()
	s.add((a << BitVecVal(0b00010, 5)) == BitVecVal(0b00100, 5))
	model = s.solve()
	print("Model:", model, "\n")

	s = Solver()
	s.add((a >> BitVecVal(0b00100, 5)) == BitVecVal(0b00001, 5))
	model = s.solve()
	print("Model:", model, "\n")

	s = Solver()
	a = BitVec("A", 32)
	s.add(a * a == BitVecVal(169, 32))
	model = s.solve()
	print("Model:", model, "\n")

	s = Solver()
	a = BitVec("A", 5)
	b = BitVec("B", 1)
	s.add(b == (a < BitVecVal(3, 5)))
	s.add(a == BitVecVal(1, 5))
	model = s.solve()
	print("Model:", model, "\n")

	s = Solver()
	a = BitVec("A", 5)
	b = BitVec("B", 1)
	s.add(b == (a > BitVecVal(3, 5)))
	s.add(a == BitVecVal(4, 5))
	model = s.solve()
	print("Model:", model, "\n")

	s = Solver()
	a = BitVec("A", 5)
	b = BitVec("B", 1)
	s.add(b == (a >= BitVecVal(3, 5)))
	s.add(a == BitVecVal(2, 5))
	model = s.solve()
	print("Model:", model, "\n")

	s = Solver()
	a = BitVec("A", 5)
	b = BitVec("B", 1)
	s.add(b == (a <= BitVecVal(3, 5)))
	s.add(a == BitVecVal(4, 5))
	model = s.solve()
	print("Model:", model, "\n")
