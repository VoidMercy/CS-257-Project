import numpy as np
from ExprNode import *
import ExprNode
import time
from BitBlaster import Solver as bSolver
from LPSolver import Solver as lpSolver
import random
import math
import z3

def square0(solver_classes, n_bits=24):
	# Z^2 = A^2 + B^2 where a solution does not exist
	# Fix A and B, and solve for Z
	A, B = random.randint(0, 2**(n_bits/2 - 1)), random.randint(0, 2**(n_bits/2 - 1))
	while int(math.sqrt(A**2 + B**2)) == math.ceil(math.sqrt(A**2 + B**2)):
		A, B = random.randint(0, 2**(n_bits/2 - 1)), random.randint(0, 2**(n_bits/2 - 1))
	assert (A**2 + B**2) < 2**n_bits

	print(A, B, math.sqrt(A**2 + B**2))
	times = []
	models = []
	for solver_class in solver_classes:
		if solver_class == z3.Solver:
			BitVec = z3.BitVec
		else:
			BitVec = ExprNode.BitVec
		s = solver_class()
		Av = BitVec("A", n_bits)
		Bv = BitVec("B", n_bits)
		Z = BitVec("Z", n_bits)
		s.add(Av * Av + Bv * Bv == Z * Z)
		s.add(Av == A)
		s.add(Bv == B)
		start = time.time()
		if solver_class == z3.Solver:
			sat = s.check()
			if sat == z3.sat:
				ret = s.model()
			else:
				ret = None	
		else:
			ret = s.solve()
		end = time.time()
		models.append(ret)
		times.append(end - start)
	return models, times
def square1(solver_classes, n_bits=24):
	# Z^2 = A^2 + B^2 where a solution does not exist
	# Fix A and B, and solve for Z
	A, B = random.randint(0, 2**(n_bits/2 - 1)), random.randint(0, 2**(n_bits/2 - 1))
	while int(math.sqrt(A**2 + B**2)) != math.ceil(math.sqrt(A**2 + B**2)):
		A, B = random.randint(0, 2**(n_bits/2 - 1)), random.randint(0, 2**(n_bits/2 - 1))
	assert (A**2 + B**2) < 2**n_bits

	print(A, B, math.sqrt(A**2 + B**2))
	times = []
	models = []
	for solver_class in solver_classes:
		if solver_class == z3.Solver:
			BitVec = z3.BitVec
		else:
			BitVec = ExprNode.BitVec
		s = solver_class()
		Av = BitVec("A", n_bits)
		Bv = BitVec("B", n_bits)
		Z = BitVec("Z", n_bits)
		s.add(Av * Av + Bv * Bv == Z * Z)
		s.add(Av == A)
		s.add(Bv == B)
		start = time.time()
		if solver_class == z3.Solver:
			sat = s.check()
			if sat == z3.sat:
				ret = s.model()
			else:
				ret = None	
		else:
			ret = s.solve()
		end = time.time()
		models.append(ret)
		times.append(end - start)
	return models, times
def quadratic(solver_classes, n_bits=16):
	# (X - A) (X - B) == 0
	# X^2 - (A+B)*X + A*B
	A, B = random.randint(0, 2**(n_bits/2 - 1)), random.randint(0, 2**(n_bits/2 - 1))
	while max(A, B)**2 - (A+B)*max(A, B) + A*B >= 2**n_bits:
		A, B = random.randint(0, 2**(n_bits/2 - 1)), random.randint(0, 2**(n_bits/2 - 1))

	print(A, B)
	times = []
	models = []
	for solver_class in solver_classes:
		if solver_class == z3.Solver:
			BitVec = z3.BitVec
		else:
			BitVec = ExprNode.BitVec
		s = solver_class()
		X = BitVec("X", n_bits)
		s.add(X*X - X*(A+B) + (A*B) == 0)
		start = time.time()
		if solver_class == z3.Solver:
			sat = s.check()
			if sat == z3.sat:
				ret = s.model()
			else:
				ret = None	
		else:
			ret = s.solve()
		end = time.time()
		models.append(ret)
		times.append(end - start)
	return models, times
def linear1(solver_class):
	s = solver_class()
def gcd(solver_class):
	s = solver_class()
def m13(solver_classes, n_bits=26):
	A, B = random.randint(0, 2**(n_bits/2)), random.randint(0, 2**(n_bits/2))
	assert A * B < 2**n_bits

	print(A, B, A * B)
	times = []
	models = []
	for solver_class in solver_classes:
		if solver_class == z3.Solver:
			BitVec = z3.BitVec
		else:
			BitVec = ExprNode.BitVec
		s = solver_class()
		Av = BitVec("A", n_bits)
		Bv = BitVec("B", n_bits)
		s.add(Av * Bv == (A * B))
		s.add(Av >= 2)
		s.add(Bv >= 2)
		start = time.time()
		if solver_class == z3.Solver:
			sat = s.check()
			if sat == z3.sat:
				ret = s.model()
			else:
				ret = None	
		else:
			ret = s.solve()
		end = time.time()
		models.append(ret)
		times.append(end - start)
	return models, times
def m16(solver_classes):
	return m13(solver_classes, n_bits=32)
def matmul(solver_classes, n_bits=32, N=2):
	models = []
	times = []
	MAX = 2000
	BITS = n_bits

	array = np.random.randint(0, MAX, size=(N, N))
	x = np.random.randint(0, MAX, size=(N, 1))
	print("X", x)
	b = array @ x
	for i in b:
		assert i < 2**(BITS)

	for solver_class in solver_classes:
		if solver_class == z3.Solver:
			BitVec = z3.BitVec
			BitVecVal = z3.BitVecVal
		else:
			BitVec = ExprNode.BitVec
			BitVecVal = ExprNode.BitVecVal
		s = solver_class()
		variables = [BitVec("A" + str(i), BITS) for i in range(N)]
		for row in range(N):
			expression = []
			for col in range(N):
				expression.append(BitVecVal(int(array[row][col]), BITS) * variables[col])
			expression = reduce(lambda x,y:x + y, expression)
			s.add(expression == BitVecVal(int(b[row]), BITS))
		start = time.time()
		if solver_class == z3.Solver:
			sat = s.check()
			if sat == z3.sat:
				ret = s.model()
			else:
				ret = None	
		else:
			ret = s.solve()
		end = time.time()
		models.append(ret)
		times.append(end - start)
	return models, times

if __name__ == "__main__":
	# print(square0([bSolver, lpSolver, z3.Solver]))
	# print(square1([bSolver, lpSolver, z3.Solver]))
	# print(quadratic([bSolver, lpSolver, z3.Solver]))
	# print(m13([bSolver, lpSolver, z3.Solver]))
	for n in range(1, 20):
		print("N", n)
		print(matmul([lpSolver, z3.Solver]))
