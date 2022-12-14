import numpy as np
from ExprNode import *
import ExprNode
import time
from BitBlaster import Solver as bSolver
from LPSolver import Solver as lpSolver
import random
import math
import z3

def segmented_sieve_primes_below(n):
  SEGMENT_SIZE = 10**6

  primes = []
  segment_start = 2
  while len(primes) == 0 or primes[-1] < n:
    segments = [0]*SEGMENT_SIZE

    # first fill out the existing primes
    for p in primes:
      c = (segment_start / p) * p
      if segment_start % p != 0:
        c += p
      c -= segment_start
      while c < SEGMENT_SIZE:
        segments[c] = 1
        c += p
    
    # go through array and each zero index is prime
    for c in range(SEGMENT_SIZE):
      if segments[c] == 0:
        cur_prime = segment_start + c
        primes.append(cur_prime)
        if cur_prime >= n:
          break
        # fill in multiples
        i = c
        while i < SEGMENT_SIZE:
          segments[i] = 1
          i += cur_prime

    segment_start += SEGMENT_SIZE
  while primes[-1] >= n:
    primes.pop(-1)
  return primes

def square0(solver_classes, n_bits=24):
	# Z^2 = A^2 + B^2 where a solution does not exist
	# Fix A and B, and solve for Z
	A, B = random.randint(0, 2**(n_bits/2 - 1)), random.randint(0, 2**(n_bits/2 - 1))
	while int(math.sqrt(A**2 + B**2)) == math.ceil(math.sqrt(A**2 + B**2)):
		A, B = random.randint(0, 2**(n_bits/2 - 1)), random.randint(0, 2**(n_bits/2 - 1))
	assert (A**2 + B**2) < 2**n_bits

	# print(A, B, math.sqrt(A**2 + B**2))
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

	# print(A, B, math.sqrt(A**2 + B**2))
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

	# print(A, B)
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
def multiplier(solver_classes, n_bits=22, sat=1):
	A, B = random.randint(0, 2**(n_bits/2)), random.randint(0, 2**(n_bits/2))
	assert A * B < 2**n_bits

	if sat == 1:
		C = A * B
	else:
		C = random.choice(segmented_sieve_primes_below(2**(n_bits/2)))
	# print(A, B, C)
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
		s.add(Av * Bv == C)
		s.add(Av >= 2)
		s.add(Bv >= 2)
		s.add(Av <= int(2**(n_bits/2)))
		s.add(Bv <= int(2**(n_bits/2)))
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
def matmul(solver_classes, n_bits=32, N=2):
	models = []
	times = []
	MAX = 2000
	BITS = n_bits

	array = np.random.randint(0, MAX, size=(N, N))
	x = np.random.randint(0, MAX, size=(N, 1))
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

# SQ0 [0.4883315706253052, 0.0017493152618408203, 0.0021961832046508787]

"""
matmul 1 [0.9321955045064291, 0.02475285530090332, 0.003245671590169271]
matmul 2 [3.7671753565470376, 0.0007696946461995443, 0.006344715754191081]
matmul 3 [8.876847823460897, 0.0011340777079264324, 0.12053473790486653]
matmul 4 [15.645793755849203, 0.0014410813649495442, 0.16335535049438477]
matmul 5 [24.815379063288372, 0.0015982786814371746, 0.21020682652791342]
matmul 6 [36.78028583526611, 0.001818259557088216, 0.27493659655253094]
matmul 7 [49.88251447677612, 0.0025201638539632163, 0.43039457003275555]
matmul 8 [65.85740892092387, 0.0023581981658935547, 0.6885140736897787]
matmul 9 [82.88272039095561, 0.0028095245361328125, 0.9863185882568359]
matmul 10 [101.30602526664734, 0.003292083740234375, 1.2145522435506184]
matmul 11 [152.21743631362915, 0.003747224807739258, 4.545188824335734]
matmul 12 [148.83437204360962, 0.004244009653727214, 2.354781150817871]
matmul 13 [174.74127705891928, 0.004980166753133138, 2.472107728322347]
matmul 14 [205.41673509279886, 0.005491971969604492, 6.498672326405843]
matmul 15 [231.02508020401, 0.006362199783325195, 6.8041815757751465]
matmul 16 [368.76359208424884, 0.007472832997639974, 35.8547879854838]
matmul 17 [331.6013397375743, 0.008130947748819986, 24.172022422154743]
matmul 18 [383.0321047306061, 0.00936579704284668, 42.5036293665568]
matmul 19 [432.5959855715434, 0.010625521341959635, 63.531824032465614]
"""

COUNT = 1

if __name__ == "__main__":
	# times = [0]*3
	# for i in range(COUNT):
	# 	res = square0([bSolver, lpSolver, z3.Solver])[1]
	# 	times = [times[i] + res[i] for i in range(3)] 
	# times = [i / float(COUNT) for i in times]
	# print("SQ0", times)

	# times = [0]*3
	# for i in range(COUNT):
	# 	res = square1([bSolver, lpSolver, z3.Solver])[1]
	# 	times = [times[i] + res[i] for i in range(3)] 
	# times = [i / float(COUNT) for i in times]
	# print("SQ1", times)

	# times = [0]*3
	# for i in range(COUNT):
	# 	res = quadratic([bSolver, lpSolver, z3.Solver])[1]
	# 	times = [times[i] + res[i] for i in range(3)] 
	# times = [i / float(COUNT) for i in times]
	# print("QUA", times)

	# times = [0]*3
	# for i in range(COUNT):
	# 	res = multiplier([bSolver, lpSolver, z3.Solver], sat=1)[1]
	# 	times = [times[i] + res[i] for i in range(3)] 
	# times = [i / float(COUNT) for i in times]
	# print("M1", times)

	# times = [0]*3
	# for i in range(COUNT):
	# 	res = multiplier([bSolver, lpSolver, z3.Solver], sat=0)[1]
	# 	times = [times[i] + res[i] for i in range(3)] 
	# times = [i / float(COUNT) for i in times]
	# print("M0", times)

	for n in range(20, 25):
		# print("N", n)
		times = [0]*2
		for i in range(COUNT):
			res = matmul([lpSolver, z3.Solver], N=n)[1]
			times = [times[i] + res[i] for i in range(2)] 
		times = [i / float(COUNT) for i in times]
		print("matmul", n, times)
