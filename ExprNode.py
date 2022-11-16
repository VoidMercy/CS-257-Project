from typing import List
from enum import Enum

class NodeType(Enum):
    FUNCTION = 0
    VARIABLE = 1
    CONSTANT = 2

class FunctionEnum(Enum):
    AND = 0
    NOT = 1
    BITWISE_OR = 2
    ADD = 3
    LSHIFT = 4
    RSHIFT = 5
    SUBTRACT = 6
    MULTIPLY = 7
    EXTRACT = 8
    CONCAT = 9
    XOR = 10
    EQUALS = 11

class ExprNode:
    def __init__(self):
        pass

class FunctionNode(ExprNode):
    def __init__(self, func_type, children):
        self.func_type = func_type
        self.children = children
    def __str__(self):
        if self.func_type == FunctionEnum.ADD:
            return "({} + {})".format(self.children[0], self.children[1])
        elif self.func_type == FunctionEnum.XOR:
            return "({} ^ {})".format(self.children[0], self.children[1])
        elif self.func_type == FunctionEnum.EQUALS:
            return "({} == {})".format(self.children[0], self.children[1])

class VariableNode(ExprNode):
    def __init__(self, name, width):
        self.name = name
        self.width = width
    def __str__(self):
        return "{}:{}".format(self.name, self.width)

class ConstantNode(ExprNode):
    def __init__(self, value, width):
        self.value = value
        self.width = width
    def __str__(self):
        return "{}:{}".format(self.value, self.width)

# Input: a list of expression nodes which need to be True
# Output: False for unsat, Model for sat. Model format TBD
def TheoryDecide(expression : List[ExprNode]):
    return False
# ((A ^ B) + C) || (D + E)
# F = ((A ^ B) + C) <- atomic
# G = (D + E)       <- atomic
# F || G
# F == 1, G == 0
# TheoryDecide([F]) -> returns True

# (A ^ B) + C == 3
a = VariableNode("A", 5)
b = VariableNode("B", 5)
c = VariableNode("C", 5)
const = ConstantNode(3, 5)
xor_part = FunctionNode(FunctionEnum.XOR, [a, b])
add_part = FunctionNode(FunctionEnum.ADD, [xor_part, c])
e = FunctionNode(FunctionEnum.EQUALS, [add_part, const])
print(e)