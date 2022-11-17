from enum import Enum

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
    LEQ = 17
    GEQ = 18

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
    FunctionEnum.LEQ : "<=",
    FunctionEnum.GEQ : ">="
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

class FunctionNode(ExprNode):
    def __init__(self, func_type, children):
        self.func_type = func_type
        self.children = children

        if self.func_type == FunctionEnum.EQUALS:
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

class ConstantNode(ExprNode):
    def __init__(self, value, width):
        self.value = value & ((1 << width) - 1)
        self.width = width
    def __str__(self):
        return "{}:{}".format(bin(self.value)[2:].zfill(self.width), self.width)
    def __repr__(self):
        return str(self)

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
