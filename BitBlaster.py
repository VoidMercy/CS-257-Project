import z3
from ExprNode import *
from PropNode import *
from typing import List, Tuple
from functools import reduce

class Solver:
	def __init__(self):
		self.conjunction = [] # Conjunction of ExprNodes

	def add(self, expression:ExprNode):
		self.conjunction.append(expression)

	def solve(self):
		expression = reduce(lambda x,y: And(x, y), self.conjunction)
		print("Expression", expression)
		self.theory_prop_map : dict[VariableNode, List[PropVariable]] = {}
		prop_vars, equation, variables = self.BitBlast(expression)
		assert len(prop_vars) == 1
		equation = PropAnd(equation, prop_vars[0])
		print(equation)
		print(self.theory_prop_map)

		# SAT solve with z3
		model = self.z3_solve(variables, equation)
		if model is None:
			return False
		else:
			return model

	def BitBlast(self, node:ExprNode, v_idx=0) -> Tuple[List[PropNode], PropNode, List[str]]:
		if isinstance(node, ConstantNode):
			return [PropConstant(int(i)) for i in bin(node.value)[2:].zfill(node.width)], PropConstant(1), []

		elif isinstance(node, VariableNode):
			new_variables = [PropVariable("v{}".format(i + v_idx)) for i in range(node.width)]
			self.theory_prop_map[node] = new_variables
			return new_variables, PropConstant(1), new_variables

		else:
			if node.func_type == FunctionEnum.EQUALS:
				left_vector, left_equation, left_variables    = self.BitBlast(node.children[0], v_idx)
				right_vector, right_equation, right_variables = self.BitBlast(node.children[1], v_idx + len(left_variables))
				variables                                     = left_variables + right_variables
				equation                                      = PropAnd(left_equation, right_equation)

				eq_var = PropVariable("v{}".format(v_idx + len(variables)))
				eq_equation = PropConstant(1)
				for i in range(node.width):
					eq_equation = PropAnd(eq_equation, PropIff(left_vector[i], right_vector[i]))
				equation = PropAnd(equation, PropIff(eq_var, eq_equation))
				return [eq_var], equation, variables + [eq_var]

			elif node.func_type == FunctionEnum.BITWISE_AND:
				left_vector, left_equation, left_variables    = self.BitBlast(node.children[0], v_idx)
				right_vector, right_equation, right_variables = self.BitBlast(node.children[1], v_idx + len(left_variables))
				variables                                     = left_variables + right_variables
				equation                                      = PropAnd(left_equation, right_equation)

				new_variables = [PropVariable("v{}".format(i + v_idx + len(variables))) for i in range(node.width)]
				for i in range(node.width):
					equation = PropAnd(equation, PropIff(new_variables[i], PropAnd(left_vector[i], right_vector[i])))
				return new_variables, equation, variables + new_variables

			elif node.func_type == FunctionEnum.BITWISE_OR:
				left_vector, left_equation, left_variables    = self.BitBlast(node.children[0], v_idx)
				right_vector, right_equation, right_variables = self.BitBlast(node.children[1], v_idx + len(left_variables))
				variables                                     = left_variables + right_variables
				equation                                      = PropAnd(left_equation, right_equation)

				new_variables = [PropVariable("v{}".format(i + v_idx + len(variables))) for i in range(node.width)]
				for i in range(node.width):
					equation = PropAnd(equation, PropIff(new_variables[i], PropOr(left_vector[i], right_vector[i])))
				return new_variables, equation, variables + new_variables

			elif node.func_type == FunctionEnum.BITWISE_XOR:
				left_vector, left_equation, left_variables    = self.BitBlast(node.children[0], v_idx)
				right_vector, right_equation, right_variables = self.BitBlast(node.children[1], v_idx + len(left_variables))
				variables                                     = left_variables + right_variables
				equation                                      = PropAnd(left_equation, right_equation)

				new_variables = [PropVariable("v{}".format(i + v_idx + len(variables))) for i in range(node.width)]
				for i in range(node.width):
					equation = PropAnd(equation, PropIff(new_variables[i], PropXor(left_vector[i], right_vector[i])))
				return new_variables, equation, variables + new_variables

			elif node.func_type == FunctionEnum.BITWISE_NOT:
				left_vector, left_equation, left_variables    = self.BitBlast(node.children[0], v_idx)
				variables                                     = left_variables
				equation                                      = left_equation

				new_variables = [PropVariable("v{}".format(i + v_idx + len(variables))) for i in range(node.width)]
				for i in range(node.width):
					equation = PropAnd(equation, PropIff(new_variables[i], PropNot(left_vector[i])))
				return new_variables, equation, variables + new_variables

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

a = BitVec("A", 5)
b = BitVec("B", 5)
c = BitVec("C", 5)
s = Solver()

s.add(BitVecVal(5, 5) & a == BitVecVal(1, 5))
model = s.solve()
print("Model:", model)

s = Solver()
s.add(BitVecVal(0, 5) | a == BitVecVal(3, 5))
model = s.solve()
print("Model:", model)

s = Solver()
s.add(BitVecVal(5, 5) ^ a == BitVecVal(3, 5))
model = s.solve()
print("Model:", model)

s = Solver()
s.add(~a == BitVecVal(3, 5))
model = s.solve()
print("Model:", model)
