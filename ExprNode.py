from enum import Enum
from functools import reduce

class NodeType(Enum):
    FUNCTION = 0
    VARIABLE = 1
    CONSTANT = 2

class FunctionEnum(Enum):
    AND = 0
    NOT = 1
    OR = 2
    BITWISE_AND = 3
    BITWISE_NOT = 4
    BITWISE_OR = 5
    BITWISE_XOR = 6
    LSHIFT = 7
    RSHIFT = 8
    SUBTRACT = 9
    ADD = 10
    MULTIPLY = 11
    EXTRACT = 12
    CONCAT = 13
    EQUALS = 14
    LT = 15
    GT = 16
    LE = 17
    GE = 18

two_operand_mapping = {
    FunctionEnum.AND : "&&",
    FunctionEnum.OR  : "||",
    FunctionEnum.BITWISE_AND : "&",
    FunctionEnum.BITWISE_OR : "|",
    FunctionEnum.BITWISE_XOR : "^",
    FunctionEnum.LSHIFT : "<<",
    FunctionEnum.RSHIFT : ">>",
    FunctionEnum.SUBTRACT : "-",
    FunctionEnum.ADD : "+",
    FunctionEnum.MULTIPLY : "*",
    FunctionEnum.EQUALS : "==",
    FunctionEnum.CONCAT : "CONCAT",
    FunctionEnum.LT : "<",
    FunctionEnum.GT : ">",
    FunctionEnum.LE : "<=",
    FunctionEnum.GE : ">="
}

class ExprNode:
    def __init__(self):
        self.width = None
    def __and__(self, other):
        return FunctionNode(FunctionEnum.BITWISE_AND, [self, other])
    def __invert__(self):
        return FunctionNode(FunctionEnum.BITWISE_NOT, [self])
    def __or__(self, other):
        return FunctionNode(FunctionEnum.BITWISE_OR, [self, other])
    def __xor__(self, other):
        return FunctionNode(FunctionEnum.BITWISE_XOR, [self, other])
    def __lshift__(self, other):
        return FunctionNode(FunctionEnum.LSHIFT, [self, other])
    def __rshift__(self, other):
        return FunctionNode(FunctionEnum.RSHIFT, [self, other])
    def __sub__(self, other):
        return FunctionNode(FunctionEnum.SUBTRACT, [self, other])
    def __add__(self, other):
        return FunctionNode(FunctionEnum.ADD, [self, other])
    def __mul__(self, other):
        return FunctionNode(FunctionEnum.MULTIPLY, [self, other])
    def __eq__(self, other):
        return FunctionNode(FunctionEnum.EQUALS, [self, other])
    def __lt__(self, other):
        return FunctionNode(FunctionEnum.LT, [self, other])
    def __le__(self, other):
        return FunctionNode(FunctionEnum.LE, [self, other])
    def __gt__(self, other):
        return FunctionNode(FunctionEnum.GT, [self, other])
    def __ge__(self, other):
        return FunctionNode(FunctionEnum.GE, [self, other])

class FunctionNode(ExprNode):
    def __init__(self, func_type, children):
        self.func_type = func_type
        self.children = children
        children_width = None
        for i in children:
            if isinstance(i, ExprNode):
                children_width = i.width
        assert children_width is not None
        for i in range(len(children)):
            if isinstance(children[i], int):
                children[i] = BitVecVal(children[i], children_width)

        if self.func_type in set([FunctionEnum.EQUALS, FunctionEnum.LT, FunctionEnum.GT, FunctionEnum.LE, FunctionEnum.GE]):
            self.width = 1
        elif self.func_type == FunctionEnum.EXTRACT:
            self.width = children[1] - children[2] + 1
        elif self.func_type == FunctionEnum.CONCAT:
            self.width = self.children[0].width + self.children[1].width
        elif self.func_type in two_operand_mapping:
            assert self.children[0].width == self.children[1].width
            self.width = self.children[0].width
        else:
            self.width = self.children[0].width
        # if self.func_type in two_operand_mapping and isinstance(self.children[1], ConstantNode) and not isinstance(self.children[0], ConstantNode):
        #     self.children[0], self.children[1] = self.children[1], self.children[0]

    def __str__(self):
        if self.func_type in two_operand_mapping:
            return "({} {} {})".format(self.children[0], two_operand_mapping[self.func_type], self.children[1])
        elif self.func_type == FunctionEnum.BITWISE_NOT:
            return "~{}".format(self.children[0])
        elif self.func_type == FunctionEnum.NOT:
            return "!{}".format(self.children[0])
        elif self.func_type == FunctionEnum.EXTRACT:
            return "Extract({}, {}, {})".format(self.children[0], self.children[1], self.children[2])
        elif self.func_type == FunctionEnum.CONCAT:
            return "Concat({}, {})".format(self.children[0], self.children[1])

    def get_variables(self):
        return reduce(lambda x,y:x | y, [i.get_variables() if isinstance(i, ExprNode) else set() for i in self.children])

    # Move constants up the tree and simplify them
    def constant_simplify(self):
        for i in range(len(self.children)):
            if isinstance(self.children[i], ExprNode):
                self.children[i] = self.children[i].constant_simplify()
        if isinstance(self.children[0], ConstantNode) and isinstance(self.children[1], ConstantNode):
            if self.func_type == FunctionEnum.ADD:
                return ConstantNode((self.children[0].value + self.children[1].value) & ((1 << self.children[0].width) - 1), self.children[0].width)
            elif self.func_type == FunctionEnum.SUBTRACT:
                return ConstantNode((self.children[0].value - self.children[1].value) & ((1 << self.children[0].width) - 1), self.children[0].width)
            elif self.func_type == FunctionEnum.MULTIPLY:
                return ConstantNode((self.children[0].value * self.children[1].value) & ((1 << self.children[0].width) - 1), self.children[0].width)
        if isinstance(self.children[0], ConstantNode):
            self.children[0], self.children[1] = self.children[1], self.children[0]
        # Constant collapse (x + A) + B into x + (A + B)
        if self.func_type in set([FunctionEnum.ADD, FunctionEnum.SUBTRACT]) and isinstance(self.children[1], ConstantNode) and isinstance(self.children[0], FunctionNode) and isinstance(self.children[0].children[1], ConstantNode) and self.children[0].func_type in set([FunctionEnum.ADD, FunctionEnum.SUBTRACT]):
            self.children[0], self.children[1] = self.children[0].children[0], FunctionNode(self.func_type, [FunctionNode(self.children[0].func_type, [0, self.children[0].children[1]]).constant_simplify(), self.children[1]]).constant_simplify()
            self.func_type = FunctionEnum.ADD
        # Move constant up the tree
        if self.func_type in set([FunctionEnum.ADD, FunctionEnum.SUBTRACT]) and not isinstance(self.children[1], ConstantNode) and isinstance(self.children[0], FunctionNode) and isinstance(self.children[0].children[1], ConstantNode) and self.children[0].func_type in set([FunctionEnum.ADD, FunctionEnum.SUBTRACT]):
            self.children[0].func_type, self.func_type = self.func_type, self.children[0].func_type
            self.children[0].children[1], self.children[1] = self.children[1], self.children[0].children[1]
        return self

    def distribute_constants(self):
        if self.func_type == FunctionEnum.MULTIPLY and isinstance(self.children[0], ConstantNode) and isinstance(self.children[1], FunctionNode) and self.children[1].func_type in set([FunctionEnum.ADD, FunctionEnum.SUBTRACT]):
            self.children[1].children[0] = FunctionNode(FunctionEnum.MULTIPLY, [self.children[0], self.children[1].children[0]])
            self.children[1].children[1] = FunctionNode(FunctionEnum.MULTIPLY, [self.children[0], self.children[1].children[1]])
            for i in range(len(self.children)):
                self.children[i] = self.children[i].distribute_constants()
            return self.children[1].distribute_constants()
        for i in range(len(self.children)):
            self.children[i] = self.children[i].distribute_constants()
        return self

    # Rotate to a left-skewed tree
    def tree_rotation(self):
        if isinstance(self.children[1], FunctionNode) and self.func_type in set([FunctionEnum.ADD, FunctionEnum.SUBTRACT]) and self.children[1].func_type in set([FunctionEnum.ADD, FunctionEnum.SUBTRACT]):
            if self.func_type == FunctionEnum.SUBTRACT and self.children[1].func_type == FunctionEnum.SUBTRACT:
                return FunctionNode(FunctionEnum.ADD, [self.children[0] - self.children[1].children[0], self.children[1].children[1]]).tree_rotation()
            elif self.func_type == FunctionEnum.ADD:
                return FunctionNode(self.children[1].func_type, [self.children[0] + self.children[1].children[0], self.children[1].children[1]]).tree_rotation()
            elif self.func_type == FunctionEnum.SUBTRACT and self.children[1].func_type == FunctionEnum.ADD:
                return FunctionNode(FunctionEnum.SUBTRACT, [self.children[0] - self.children[1].children[0], self.children[1].children[1]]).tree_rotation()
        for i in range(len(self.children)):
            self.children[i] = self.children[i].tree_rotation()
        return self

    # Move everything to one side
    def equation_skew(self):
        if self.func_type in set([FunctionEnum.EQUALS, FunctionEnum.LT, FunctionEnum.GT, FunctionEnum.LE, FunctionEnum.GE]):
            self.children[0] = self.children[0] - self.children[1]
            self.children[1] = ConstantNode(0, self.children[1].width)

    def extract_constant(self):
        if self.func_type in set([FunctionEnum.EQUALS, FunctionEnum.LT, FunctionEnum.GT, FunctionEnum.LE, FunctionEnum.GE]):
            if isinstance(self.children[0], FunctionNode) and isinstance(self.children[0].children[1], ConstantNode):
                return FunctionNode(FunctionEnum.SUBTRACT, [0, FunctionNode(self.children[0].func_type, [0, self.children[0].children[1]])]).constant_simplify()
            else:
                return self.children[1]
        return None

class VariableNode(ExprNode):
    def __init__(self, name, width):
        self.name = name
        self.width = width
    def __str__(self):
        return "{}:{}".format(self.name, self.width)
    def __repr__(self):
        return str(self)
    def __hash__(self):
        return hash((self.name, self.width))
    def get_variables(self):
        return set([self.name])
    def constant_simplify(self):
        return self
    def distribute_constants(self):
        return self
    def tree_rotation(self):
        return self

class ConstantNode(ExprNode):
    def __init__(self, value, width):
        self.value = value & ((1 << width) - 1)
        self.width = width
    def __str__(self):
        # return "{}:{}".format(bin(self.value)[2:].zfill(self.width), self.width)
        return "{}:{}".format(str(self.value), self.width)
    def __repr__(self):
        return str(self)
    def get_variables(self):
        return set()
    def constant_simplify(self):
        return self
    def distribute_constants(self):
        return self
    def tree_rotation(self):
        return self

# Helper Functions that use z3-like API
def BitVec(name, width):
    return VariableNode(name, width)
def BitVecVal(value, width):
    return ConstantNode(value, width)
def And(a, b):
    return FunctionNode(FunctionEnum.AND, [a, b])
def Or(a, b):
    return FunctionNode(FunctionEnum.OR, [a, b])
def Not(a):
    return FunctionNode(FunctionEnum.NOT, [a])
def Extract(a, i, j):
    if type(i) is not int or type(j) is not int:
        raise Exception("Extract on non-constant indices not supported")
    if i < 0 or i >= a.width or j < 0 or j >= a.width:
        raise Exception("Indices out of range")
    return FunctionNode(FunctionEnum.EXTRACT, [a, i, j])
def Concat(a, b):
    return FunctionNode(FunctionEnum.CONCAT, [a, b])

# ((A ^ B) + C) || (D + E)
# F = ((A ^ B) + C) <- atomic
# G = (D + E)       <- atomic
# F || G
# F == 1, G == 0
# TheoryDecide([F]) -> returns True

#Example:
#(A ^ B) + C == 3

if __name__ == "__main__":
    a = BitVec("A", 5)
    b = BitVec("B", 5)
    c = BitVec("C", 5)
    e = ((a ^ b) + c) == BitVecVal(3, 5)
    print(e)
