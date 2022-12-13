from enum import Enum
import z3
from functools import reduce

def PropAnd(a, b):
	# Optimizations
	if isinstance(b, PropConstant):
		a, b = b, a
	if isinstance(a, PropConstant):
		if a.v == 0:
			return PropConstant(0)
		else:
			return b
	return PropFunction(PropEnum.AND, a, b)
def PropOr(a, b):
	if isinstance(b, PropConstant):
		a, b = b, a
	if isinstance(a, PropConstant):
		if a.v == 0:
			return b
		else:
			return PropConstant(1)
	return PropFunction(PropEnum.OR, a, b)
def PropNot(a):
	if isinstance(a, PropConstant):
		return PropConstant(a.v ^ 1)
	if isinstance(a, PropFunction) and a.op == PropEnum.NOT:
		return a.left
	return PropFunction(PropEnum.NOT, a, None)

def PropIff(a, b):
	return PropOr(PropAnd(a, b), PropAnd(PropNot(a), PropNot(b)))
def PropXor(a, b):
	return PropOr(PropAnd(PropNot(a), b), PropAnd(a, PropNot(b)))
def PropMux(choose, a, b):
	return PropOr(PropAnd(choose, a), PropAnd(PropNot(choose), b))
def PropFullAdder(a, b, cin):
	s    = reduce(PropXor, [a, b, cin])
	cout = reduce(PropOr, [PropAnd(a, b), PropAnd(a, cin), PropAnd(b, cin)])
	return s, cout

class PropEnum(Enum):
    AND = 0
    NOT = 1
    OR = 2

class PropNode:
	def __init__(self):
		pass

	def __eq__(self, other):
		if isinstance(self, PropVariable) and isinstance(other, PropVariable):
			return self.name == other.name
		if isinstance(self, PropConstant) and isinstance(other, PropConstant):
			return self.v == other.v
		if isinstance(self, PropFunction) and isinstance(other, PropFunction):
			return (self.left == other.left) and (self.right == other.right)
		return False

	def __hash__(self):
		if isinstance(self, PropVariable): return hash(self.name)
		if isinstance(self, PropConstant): return hash(self.v)
		if isinstance(self, PropFunction): return hash((self.op, self.left.__hash__(), self.right.__hash__()))

	def __lt__(self, other):
		if isinstance(self, PropVariable) and isinstance(other, PropVariable):
			return self.name < other.name
		if isinstance(self, PropConstant) and isinstance(other, PropConstant):
			return self.v < other.v
		if isinstance(self, PropFunction) and isinstance(other, PropFunction):
			if self.left < other.left: return True
			if self.left == other.left: return self.right < other.right
			return False
		return False

class PropFunction(PropNode):
	def __init__(self, op, left, right):
		self.op = op
		self.left = left
		self.right = right

	def convert_z3(self, var_map):
		if self.op == PropEnum.AND:
			return z3.And(self.left.convert_z3(var_map), self.right.convert_z3(var_map))
		elif self.op == PropEnum.OR:
			return z3.Or(self.left.convert_z3(var_map), self.right.convert_z3(var_map))
		elif self.op == PropEnum.NOT:
			return z3.Not(self.left.convert_z3(var_map))
	def __str__(self):
		if self.op == PropEnum.AND:
			return "({} && {})".format(self.left, self.right)
		elif self.op == PropEnum.OR:
			return "({} || {})".format(self.left, self.right)
		elif self.op == PropEnum.NOT:
			return "!{}".format(self.left)
		raise Exception("Unknown op")
	def __repr__(self):
		return str(self)

class PropVariable(PropNode):
	def __init__(self, name):
		self.name = name
	def __str__(self):
		return self.name
	def __repr__(self):
		return str(self)
	def convert_z3(self, var_map):
		return var_map[self.name]

class PropConstant(PropNode):
	def __init__(self, v):
		assert v == 0 or v == 1
		self.v = v
	def __str__(self):
		return str(self.v)
	def __repr__(self):
		return str(self)
	def z3_convert(self, var_map):
		return self.v == 1

class ImplicationNode:
    def __init__(self, variable, value):
        self.variable = variable
        self.value = value
        self.level = -1
        self.parents = []
        self.children = []
        self.clause = None
