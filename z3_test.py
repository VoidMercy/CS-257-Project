from z3 import *
import numpy as np
from functools import reduce

s = Solver()

A = Int("A")
k = Int("k")
s = Solver()
s.add(A * 123124124 - k * 2**28 == 231974516)
s.add(k >= 0)
print(s.check())
print(s.model())