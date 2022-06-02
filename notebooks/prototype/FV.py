from dataclasses import dataclass
from typing import *
from random import randint, sample#, shuffle, choice, choices

from copy import deepcopy
from functools import reduce
from itertools import product

# `funcy` provides some convenient functionally-flavored combinators for manipulating collections and 
# dictionaries used throughout: https://funcy.readthedocs.io/en/stable/index.html
from funcy import * 

import z3

# UTILITIES

# To aid in generating fresh names.
# Simplest, dumbest implementation.
# More helpful for making constraint graphs interpretable would be sampling a few random (short!) words
def freshGenerator() -> str:
  start = 0
  while True:
    yield f"{start}" # no int provided (just str) because it should not be a source of global ordering!
    start += 1


# SEQUENCES

def pi(i: int):
  assert i > -1
  def projection(seq):
    assert len(seq) > i
    return seq[i]
  return projection

def p0(seq):
  return pi(0)(seq)

def p1(seq):
  return pi(1)(seq)

def p2(seq):
  return pi(2)(seq)

def fst(seq):
  return p0(seq)

def snd(seq):
  return p1(seq)

def thrd(seq):
  return p2(seq)

def ensureOrdered(collection):
  assert isinstance(collection, Sequence) or isinstance(collection, Reversible)

def ensureSameLength(a, b):
  assert len(a) == len(b)

def ensureSameLengths(seqs):
  L = len(seqs[0])
  for each in seqs:
    assert len(each) == L

def grandFoldl(binOp, initial=None):
  def f(values):
    if initial is None:
      return reduce(binOp, values)
    else:
      return reduce(binOp, values, initial)
  return f

# SUBSETS

def randomNonemptySubset(s: set, k=None) -> set:
  if k is None:
#     t       = tuple(s)
#     cap     = len(t)
#     return set(sample(population=t, k=size))
    cap     = len(s)
    size    = randint(1,cap)
  else:
    size=k
  return set(sample(population=s, k=size))

def randomInterestingSubset(maxAttempts: int, s: set, cap=None, k=None, minSpec=None) -> set:
  assert maxAttempts > 0
  assert len(s) > 0
  assert minSpec is None or minSpec > 0

  if k is None:
    if cap is None:
      cap = len(s)
    assert cap <= len(s), f"{cap} should be <= {len(s)}"
    k = randint(1,cap)
  
  if minSpec is None:
    minSpec = 1
  
  m     = len(tuple(s)[0])
  zeroV = FeatureVector.z(m)
  
  
  S = randomNonemptySubset(s, k)
  attempts = 1
  while attempts < maxAttempts and FeatureVector.spec(grandFoldl(FeatureVector.meet)(S)) < minSpec:
#   while attempts < maxAttempts and grandFoldl(FeatureVector.meet)(S) == zeroV:
    S = randomNonemptySubset(s, k)
    attempts += 1
  if grandFoldl(FeatureVector.meet)(S) == zeroV:
    return None
  else:
    return S


def allSubsetVectors(outType=None):
  def f(population_size):
    result = product((True, False), repeat=population_size)
    if outType is None:
      return result
    else:
      return outType(result)
  return f

def mk_subset_fromSubsetVector(outType=None):
  def g(orderedPopulation):
    def f(subsetVector):
      result = (each
                for include, each in zip(subsetVector, orderedPopulation)
                if include)
      if outType is None:
        return result
      else:
        return outType(result)
    return f
  return g

def mk_subsetVector_fromSubset(outType=None):
  def g(orderedPopulation):
    def f(subset):
      result = (True if each in subset else False
                for each in orderedPopulation)
      if outType is None:
        return result
      else:
        return outType(result)
    return f
  return g

def isSubsetEq(subsetVector_left, subsetVector_right):
  assert len(subsetVector_left) == len(subsetVector_right)
  left, right = subsetVector_left, subsetVector_right
  if left == right:
    return True
  else:
    return all([(not l) or (l == r)
                for l,r in zip(left, right)])

# FIXME ORPHANED TEST
# ssv_cxs = []
# for ssv in allSubsetVectors(list)(4):
#   ss_fromV         = mk_subset_fromVector(list)("ABCD")(ssv)
#   ssv_fromSS_fromV = mk_subsetVector_fromSubset(tuple)("ABCD")(ss_fromV)

#   print("---")
#   print(ssv)
#   print(ssv_fromSS_fromV)
#   print(ss_fromV)

#   if ssv_fromSS_fromV != ssv:
#     ssv_cxs.add((ssv, ssv_fromSS_fromV, ss_fromV))

# len(ssv_cxs)
# for each in ssv_cxs:
#   print(each)

# PRINTING

def showVal(valName, val):
  return f"{valName} = {val}"

def showApp(fName, argName, val):
  return f"{fName}(" + f"{argName}" + f") = {val}"

def showBinOp(leftName, opName, rightName, val):
  return f"{leftName}" + f" {opName} " + f"{rightName}" + f" = {val}"

def showBinGraphTest(op, a, b, cActual, cExpected):
  return (f"{a} {op} {b} = {cActual} vs. {cExpected}")


# CONCRETE FEATURE VALUES

@dataclass
class FeatureValue:
  value: int
  
  # validation, construction, representation...
  
  def _isWithinRange(self) -> bool:
    return self.value in (-1, 0, 1)
  
  def ensureValidity(self):
    if not self._isWithinRange():
      raise Exception(f"Input must be one of -1, 0, or 1, but self.value = '{self.value}'")
  
  def __str__(self) -> str:
    if self.value == 0:
      return "0"
    elif self.value == -1:
      return "-"
    elif self.value == 1:
      return "+"
    else:
      raise Exception(f"Input must be one of -1, 0, or 1, but self.value = '{self.value}'")
  
  #   smart constructors
  @staticmethod
  def z():
    return FeatureValue(0)
  
  @staticmethod
  def p():
    return FeatureValue(1)
  
  @staticmethod
  def n():
    return FeatureValue(-1)
  
  @staticmethod
  def r():
    return FeatureValue(randint(-1,1))
  
  @staticmethod
  def fromInt(i: int):
    if i in (-1, 0, 1):
      return FeatureValue(i)
    else:
      raise Exception(f"Input must be one of -1, 0, or 1, got '{i}'")
  
  @staticmethod
  def fromString(s: str):
    if s == "0":
      return FeatureValue(0)
    elif s == "-":
      return FeatureValue(-1)
    elif s == "+":
      return FeatureValue(1)
    else:
      raise Exception(f"Input must be one of '0', '-', or '+', got '{s}'")
      
  @staticmethod
  def fromBooleans(defined, valence):
    if not defined:
      return FeatureValue.z()
    else:
      if valence:
        return FeatureValue.p()
      else:
        return FeatureValue.n()
  
  def toString(self):
    if self.value == 0:
      return "0"
    elif self.value == -1:
      return "-"
    elif self.value == 1:
      return "+"
    else:
      raise Exception(f"Value must be one of -1, 0, or 1, got '{self.value}'")
  
  def toMaybeBool(self, zeroValue=None):
    if self.value == 0:
      return zeroValue
    elif self.value == -1:
      return False
    elif self.value == 1:
      return True
    else:
      raise Exception(f"Value must be one of -1, 0, or 1, got '{self.value}'")
  
  # queries
  
  def valence(self):
    if not self.isDefined():
      return None
    else:
      if self.value == 1:
        return True
      elif self.value == -1:
        return False
      else:
        raise Exception(f"value should be +1 or -1, got '{self.value}'")
  
  def isDefined(self) -> bool:
    return self.isSpecified()
  
  def isSpecified(self) -> bool:
    self.ensureValidity()
    return self.value != 0
  
  @staticmethod
  def comparable(left, right) -> bool:
    left.ensureValidity()
    right.ensureValidity()
    return (not (left.isSpecified() or right.isSpecified())) or (FeatureValue.flip(left) != right)
  
  def __hash__(self):
    return hash(self.value)
  
  def __eq__(self, other):
    if type(other) == FeatureValue:
      return self.value == other.value
    else:
      return False
  
  # < defining a semilattice of specification on feature vectors where bottom element is defined nowhere 
  def __le__(self, other):
    return (self == other) or (not self.isSpecified()) and other.isSpecified()
  
  def __ge__(self, other):
    return (self == other) or self.isSpecified() and not other.isSpecified()
  
  def __lt__(self, other):
    return self != other and self.__le__(other)
  
  def __gt__(self, other):
    return self != other and self.__ge__(other)
  
  # operations
  def __invert__(self):
    return FeatureValue.flip(self)
  
  def __and__(self, other):
    return FeatureValue.meet(self, other)
  
  def __or__(self, other):
    return FeatureValue.join(self, other)
  
  def __sub__(self, other):
    return FeatureValue.minus(self, other)
  
  def __rshift__(self, other):
    return FeatureValue.prunion(self, other)
  
  @staticmethod
  def identity(featureValue):
    featureValue.ensureValidity()
    return deepcopy(featureValue)
  
  @staticmethod
  def flip(featureValue):
    featureValue.ensureValidity()
    if not featureValue.isSpecified():
      return FeatureValue.z()
    else:
      return FeatureValue(-1 * featureValue.value)
  
  @staticmethod
  def minus(left, right):
    left.ensureValidity()
    right.ensureValidity()
    if left == right:
      return FeatureValue.z()
    else:
      return deepcopy(left)
    
  @staticmethod
  def erase(featureValue):
    featureValue.ensureValidity()
    return FeatureValue.z()
  
  #(right) priority union
  @staticmethod
  def prunion(left, right):
    left.ensureValidity()
    right.ensureValidity()
    return deepcopy(right) if right.isSpecified() else deepcopy(left)
  
  #FIXME
  # Given a binary operator *,
  # if
  #   a * b = c
  # then the left inverse operation is \: 
  #   a \ c = b
  # leftInv_prunion is the analogue of "\" relative to "prunion"
  @staticmethod
  def leftInv_prunion(left, result):
    pass
  
  # Given a binary operator *,
  # if
  #   a * b = c
  # then the right inverse operation is /: 
  #   c / b = a
  # rightInv_prunion is the analogue of "/" relative to "prunion"
  @staticmethod
  def rightInv_prunion(result, right):
    pass
  
  @staticmethod
  def meet(left, right):
    left.ensureValidity()
    right.ensureValidity()
    if left.isSpecified() and right.isSpecified() and left == right:
      return deepcopy(left)
    else:
      return FeatureValue.z()
    
  @staticmethod
  def meet1(featureVectors):
    return foldMeet(featureVectors)

  @staticmethod
  def foldMeet(featureVectors):
    assert len(featureVectors) > 0, f"the least element of the specification semilattice is only defined with respect to a *nonempty* subset of the semilattice"
    if len(featureVectors) == 1:
      return tuple(featureVectors)[0]
    return grandFoldl(FeatureVector.meet)(featureVectors)
  
  @staticmethod
  def glb(featureVectors):
    return foldMeet(featureVectors)
  
  @staticmethod
  def naturalClasses(featureVectors, objects):
    m = glb(featureVectors)
    raise Exception("Not finished - needs to find other concrete FVs with the same interpretation as the glb") #FIXME
    # return glb(featureVectors)

  @staticmethod
  def joinable(left, right) -> bool:
    return FeatureValue.comparable(left, right)
  
  @staticmethod
  def join(left, right):
    assert FeatureValue.joinable(left, right), f"left, right must be joinable:\nleft={left}\nright={right}"
    if left.isSpecified() and right.isSpecified():
      if left == right:
        return deepcopy(left)
      else:
        raise Exception(f"left, right must be joinable, but they have distinct specified values:\nleft={left}\nright={right}")
    elif not (left.isSpecified() or right.isSpecified()):
      return FeatureValue.z()
    elif left.isSpecified():
      return deepcopy(left)
    else:
      return deepcopy(right)
      

@dataclass
class FeatureVector:
  value: Tuple[FeatureValue]
  
  # validation, construction, representation...
  
  def ensureValidity(self):
    ensureOrdered(self.value)
    for (idx, each) in enumerate(self.value):
      if not each._isWithinRange():
        raise Exception(f"Feature vector contains invalid value @ index {idx}:\nvalue = '{each}'\nFeatureVector = {self}")
  
  def __str__(self) -> str:
    return "[" + " ".join(lmap(str, self.value)) + "]"
  
  #   smart constructors
  @staticmethod
  def z(length):
    return FeatureVector(tuple([FeatureValue.z() for each in range(length)]))
  
  @staticmethod
  def r(length):
    return FeatureVector(tuple([FeatureValue.r() for each in range(length)]))

  @staticmethod
  def randomObjects(numFeatures, numObjects):
    M               = numFeatures
    MAX_NUM_VECTORS = 3 ** M
    N = numObjects
    assert N <= (3 ** M)

    O = {FeatureVector.r(length=M) for each in range(N)}

    while len(O) < N:
      gap = N - len(O)
      O = O.union({FeatureVector.r(length=M) for each in range(gap)})

    return tuple(sorted(list(O), key=FeatureVector.sortKey))
  
  @staticmethod
  def fromInts(ints):
    return FeatureVector(tuple([FeatureValue.fromInt(each) for each in ints]))
    
  @staticmethod
  def fromString(s: str, sep: str = None):
    if sep is not None:
      assert sep in (' ', ','), f"Seperator character assumed to be ' ' or ',', got '{sep}' instead"
    else:
      sep = ' '
    assert s[ 0] == '[', f"First character of s expected to be '[', got '{s[0]}'"
    assert s[-1] == ']', f"Last character of s expected to be ']', got '{s[-1]}'"
    
    body = s[1:-1].strip()
    values = body.split(sep)
    return FeatureVector(tuple([FeatureValue.fromString(each) for each in values]))
  
  @staticmethod
  def fromBooleans(defineds, valences):
    assert len(defineds) == len(valences), f"Parameters must be of equal length: '{len(defineds)}' != '{len(valences)}'"
    return FeatureVector([FeatureValue.fromBooleans(lr[0], lr[1]) for lr in zip(defineds, valences)])
  
  def toChar(self):
    return tuple([each.toString() for each in self.value])
  
  def toBooleans(self, zeroValue=None):
    return (tuple([each.isDefined() for each in self.value]),
            tuple([each.toMaybeBool(zeroValue=zeroValue) for each in self.value]))
  
  # queries
  
  def __hash__(self):
    return hash(self.value)

  def __eq__(self, other):
    if type(other) == FeatureVector:
      return all([a == b for a,b in zip(self.value, other.value)])
    else:
      return False
  
  def __len__(self):
    return len(self.value)
  
  @staticmethod
  def spec(featureVector):
    return len([v for v in featureVector.value if v.isSpecified()])
  
  @staticmethod
  def sortKey(featureVector):
    return (FeatureVector.spec(featureVector), featureVector)
  
  def fullySpecified(self) -> bool:
    return all([each.isSpecified for each in self.value])
  
  @staticmethod
  def sameLength(left, right) -> bool:
    return len(left) == len(right)
  
  @staticmethod
  def comparable(left, right) -> bool:
    return FeatureVector.sameLength(left, right) and (FeatureVector.flip(left) != right)
  
  @staticmethod
  def ensureSameLength(left, right):
    assert FeatureVector.sameLength(left, right), f"Feature vectors are different lengths: '{len(left)}' vs. '{len(right)}'"
  
  @staticmethod
  def ensureComparable(left, right):
    FeatureVector.ensureSameLength(left, right)
    assert (left == FeatureVector.z(len(left)) and left == right) or FeatureVector.flip(left) != right, f"Feature vectors are not comparable:\n'{left}'\nvs.\n'{right}'"
  
  # < defining a semilattice of specification on feature vectors where bottom element is defined nowhere 
  def __le__(self, other):
    FeatureVector.ensureSameLength(self, other)
    return all([left <= right for (left, right) in zip(self.value, other.value)])
  
  def __lt__(self, other):
    return self != other and self.__le__(other)
  
  def __ge__(self, other):
    FeatureVector.ensureSameLength(self, other)
    return all([left >= right for (left, right) in zip(self.value, other.value)])
  
  def __gt__(self, other):
    return self != other and self.__ge__(other)
  
  # operations
  def __invert__(self):
    return FeatureVector.flip(self)
  
  def __and__(self, other):
    return FeatureVector.meet(self, other)
  
  def __or__(self, other):
    return FeatureVector.join(self, other)
  
  def __sub__(self, other):
    return FeatureVector.minus(self, other)
  
  def __rshift__(self, other):
    return FeatureVector.prunion(self, other)
  
  @staticmethod
  def _map(unaryOp):
    def newOp(featureVector):
      featureVector.ensureValidity()
      return FeatureVector(tuple(lmap(unaryOp, featureVector.value)))
    return newOp
  
  @staticmethod
  def _elementwise(binaryOp):
    def newOp(left, right):
      FeatureVector.ensureSameLength(left, right)
      return FeatureVector(tuple(lmap(lambda lr: binaryOp(lr[0], lr[1]),
                                      zip(left.value, right.value))))
    return newOp
  
  @staticmethod
  def identity(featureVector):
    featureVector.ensureValidity()
    return deepcopy(featureVector)
  
  @staticmethod
  def minus(left, right):
    return FeatureVector._elementwise(FeatureValue.minus)(left, right)
    
  @staticmethod
  def erase(featureVector):
    featureVector.ensureValidity()
    return featureVector.z(len(featureVector))
  
  @staticmethod
  def prunion(left, right):
    FeatureVector.ensureSameLength(left, right)
    return FeatureVector._elementwise(FeatureValue.prunion)(left, right)
  
  @staticmethod
  def flip(featureVector):
    return FeatureVector._map(FeatureValue.flip)(featureVector)
  
  @staticmethod
  def meet(left, right):
    FeatureVector.ensureSameLength(left, right)
    return FeatureVector._elementwise(FeatureValue.meet)(left, right)
  
  @staticmethod
  def joinable(left, right) -> bool:
    return FeatureVector.comparable(left, right)
  
  @staticmethod
  def join(left, right):
    assert FeatureVector.joinable(left, right), f"left, right must be joinable:\nleft={left}\nright={right}"
    return FeatureVector._elementwise(FeatureValue.join)(left, right)

  #FIXME left and right inverse of priority union
  
  @staticmethod
  def interpretation(featureVector, sortedObjectVectors):
    return tuple([featureVector <= o for o in sortedObjectVectors])
  

@dataclass
class FVMap:
  target: FeatureVector
  change: FeatureVector
  
  def ensureValidity(self):
    target.ensureValidity()
    change.ensureValidity()
  
  @staticmethod
  def mk(t, c):
    FeatureVector.ensureSameLength(t,c)
    return FVMap(t,c)
  
  @staticmethod
  def ULPRule(t, c):
    return FVMap.mk(t,c)
  
  def __eq__(self, other):
    if type(other) == FVMap:
      return self.target == other.target and self.change == other.change
    else:
      return False
  
  def __hash__(self):
    return hash((hash(self.target), hash(self.change)))
  
  def __str__(self) -> str:
    return f"{self.target} -> {self.change}"
  
  def toFunction(self):
    return lambda fv: self.apply(fv)
  
  def toPartialGraph(self, inputs):
    return tuple([(each, self.apply(each)) for each in inputs])
  
  # operations
  def apply(self, featureVector):
    FeatureVector.ensureSameLength(self.target, featureVector)
    if self.target <= featureVector:
      return featureVector >> self.change
    else:
      return deepcopy(featureVector)

  def __call__(self, featureVector):
#     if featureVector is None:
#       return self
    if type(featureVector) == FeatureVector:
      return self.apply(featureVector)
    else:
      raise Exception(f"FVMap can only be called on a feature vector, but got '{featureVector}'")
  
  @staticmethod
  def consistent(rule, inputVector, outputVector) -> bool:
    FeatureVector.ensureSameLength(inputVector, outputVector)
    return rule(inputVector) == outputVector
  
  @staticmethod
  def showGraph(ruleLabel, pairs) -> List[str]:
    return [showApp(ruleLabel, i, o) for (i,o) in pairs]
  
  def domGLB(self):
    return deepcopy(self.target)
  
  def codGLB(self):
    return self.target >> self.change 
  
  @staticmethod
  def inDom(featureVector, rule) -> bool:
    return rule.domGLB() <= featureVector
  
  @staticmethod
  def inCod(featureVector, rule) -> bool:
    return rule.codGLB() <= featureVector
  
  @staticmethod
  def vacuous(featureVector, rule) -> bool:
    return not FVMap.inDom(featureVector, rule)
  
  @staticmethod
  def isFixpoint(featureVector, rule) -> bool:
    return FVMap.consistent(rule, featureVector, featureVector)
  
  @staticmethod
  def isFixpoint1(featureVector, rule) -> bool:
    return inDom(featureVector, rule) and inCod(featureVector, rule)
  
  @staticmethod
  def isMutationpoint(featureVector, rule) -> bool:
    return not FVMap.isFixpoint(featureVector, rule)
  
#   @staticmethod
#   def isMutationpoint1(featureVector, rule) -> bool:
#     return inDom(featureVector, rule) and 

#FIXME inverse

# TESTING


def testBinOp_Booleans(binOpRel, binOp, numFeatures, testSet=None, exceptions=False, none=False):
  if testSet is None:
    V = {FeatureVector.fromInts(x) for x in product((-1, 0, 1), repeat=numFeatures)}
  else:
    V = testSet

  s = z3.Solver()

  symbolicFV_left  = SymbolicFV.mk(numFeatures, "l")
  symbolicFV_right = SymbolicFV.mk(numFeatures, "r")
  symbolicFV_res   = SymbolicFV.mk(numFeatures, "res")
  def_l  , val_l   = symbolicFV_left.unwrap()
  def_r  , val_r   = symbolicFV_right.unwrap()
  def_res, val_res = symbolicFV_res.unwrap()

  counterexamples = []
  for a, b in product(V,V):
    if exceptions:
      try:
        c = binOp(a,b)
      except:
        pass
      else:
        if none and c is None:
          pass
        else:
          s.push()
          s.add(SymbolicFV.eq(symbolicFV_left , a))
          s.add(SymbolicFV.eq(symbolicFV_right, b))
          # s.add(SymbolicFV.eq(def_l  , val_l  , *a.toBooleans()))
          # s.add(SymbolicFV.eq(def_r  , val_r  , *b.toBooleans()))

          s.add(binOpRel(symbolicFV_left, symbolicFV_right, symbolicFV_res))
          # s.add(binOpRel(def_l, val_l, def_r, val_r, def_res, val_res))
          if s.check() == z3.sat:
            res_symbolic = symbolicFV_res.toConcreteFeatureVector(s.model())
            if res_symbolic != c:
              counterexamples.append((a, b, c, res_symbolic))
          s.pop()
    else:
      c = binOp(a,b)
      if none and c is None:
        pass
      else:
        s.push()
        s.add(SymbolicFV.eq(symbolicFV_left , a))
        s.add(SymbolicFV.eq(symbolicFV_right, b))
        # s.add(SymbolicFV.eq(def_l  , val_l  , *a.toBooleans()))
        # s.add(SymbolicFV.eq(def_r  , val_r  , *b.toBooleans()))

        s.add(binOpRel(symbolicFV_left, symbolicFV_right, symbolicFV_res))
        # s.add(binOpRel(def_l, val_l, def_r, val_r, def_res, val_res))
        if s.check() == z3.sat:
          res_symbolic = symbolicFV_res.toConcreteFeatureVector(s.model())
          if res_symbolic != c:
            counterexamples.append((a, b, c, res_symbolic))
        s.pop()
  return counterexamples


def testStackOp_Booleans(opRel, op, numFeatures, testSet=None):
  s = z3.Solver()

  if testSet is None:
    V = {FeatureVector.fromInts(x) for x in product((-1, 0, 1), repeat=numFeatures)}
    numVectors = len(V)
#   elif testSet is "symbolic":
#     # FIXME - check on uninterpreted function symbols - are they the only vehicle for "testing" symbolic data against concrete functions?

#     #define numVectors

#     stack = [mk_FVBooleans(numFeatures, f"V{k}") for k in range(numVectors)]
#     defineds, valences = lmap(lambda pair: pair[0], stack), lmap(lambda pair: pair[1], stack)

#     #distinctness assertion

#    #
  else:
    V = testSet
    numVectors = len(V)

  result = op(V)

  # stack = [SymbolicFV.mk(numFeatures, f"V_{k}") for k in range(numVectors)]
  # defineds, valences = lmap(lambda pair: pair[0], stack), lmap(lambda pair: pair[1], stack)
  stack = SymbolicFV.mks(numFeatures, "V", numVectors)
  defineds, valences = SymbolicFV.unwraps(tuple)(stack)
  for def_v, val_v, v in zip(defineds, valences, V):
    s.add(SymbolicFV.eq(def_v, val_v, *v.toBooleans()))

  counterexamples = []

  result = SymbolicFV.mk(numFeatures, "res")
  defined_result, valence_result = result.unwrap()
  # defined_result, valence_result = mk_FVBooleans(numFeatures, f"res")
  s.add(opRel(stack, result))
  # s.add(opRel(defineds, valences, defined_result, valence_result))

  if s.check() == z3.sat:
    result_symbolic = result.toConcreteBooleans(s.model())
    if result_symbolic != result:
      counterexamples.append((V, result, result_symbolic))
  else:
    print("unsat!?")
  return counterexamples

# Symbolic Representations

# SymbolicSubsetVector
# Symbolic representation of a subset of some fixed (concrete) length set of objects
# Datatype: "newtype" wrapper around a tuple of z3 Booleans
#           - a constructor is provided
# All other functions are static methods that return constraints asserting a relation
#  holds among their arguments. Relations modeling the basic Boolean operations you'd expect are included.

@dataclass
class SymbolicSubsetVector:
  value: tuple

  def __len__(self):
    return len(self.value)

  # def __eq__(self, other):
  #   raise Exception("You probably don't want to use this kind of equality")

  def __hash__(self):
    return hash(self.value)

  def mk(numObjects: int, identifier: str):
     return SymbolicSubsetVector(tuple([z3.Bool(f"{identifier}_{i}") for i in range(numObjects)]))

  @staticmethod
  def mkFromConcreteSubsetVector(concreteSubsetVector, identifier):
    numObjects    = len(concreteSubsetVector)
    symbolicSSV   = SymbolicSubsetVector.mk(numObjects, identifier)
    eqConstraints = SymbolicSSV.eq(symbolicSSV, concreteSubsetVector)
    return symbolicSSV, eqConstraint

  @staticmethod
  def mkFromConcreteSubset(concreteFVs_subset, concreteFVs_objects, identifier):
    ensureSameLengths(   concreteFVs_subset     )
    ensureSameLengths(   concreteFVs_objects    )
    ensureSameLength(    concreteFVs_subset[0]
                    ,    concreteFVs_objects[0] )
    numInSubset   = len( concreteFVs_subset     )
    numObjects    = len( concreteFVs_objects    )
    symbolicSSV   = SymbolicSubsetVector.mk(numObjects, identifier)
    ssConstraint  = SymbolicFV.isSubseteq(concreteFVs_subset, concreteFVs_objects) #this is more of a precondition/assumption
    eqConstraints = z3.And([ symbolicSSV[i] == SymbolicFV.eq3( concreteFVs_subset
                                                             , concreteFVs_objects[i]
                                                             )
                             for i in range(numObjects)
                           ])
    constraints   = z3.And([ ssConstraint
                           , eqConstraints
                           ])
    return symbolicSSV, constraints

  def ensureValidity(self):
    ensureOrdered(self.value)

  def concrete(self, model):
    return self.toConcreteSubsetVector(model)

  def toConcreteSubsetVector(self, model):
    return tuple([model[v]
                  for v in self.value])

  @staticmethod
  def isEmpty(subsetVector):
    return z3.And([z3.Not(v)
                   for v in subsetVector.value])

  @staticmethod
  def isNonempty(subsetVector):
    return z3.Or([v
                  for v in subsetVector.value])

  @staticmethod
  def hasElement(subsetVector, i):
    assert i < len(subsetVector)
    return subsetVector.value[i]

  @staticmethod
  def missingElement(subsetVector, i):
    assert i < len(subsetVector)
    return z3.Not(subsetVector.value[i])

  # See discussion of Boolean cardinality constraints at
  #   http://theory.stanford.edu/~nikolaj/programmingz3.html#sec-boolean-theories
  @staticmethod
  def hasExactlyKelements(subsetVector, k):
    assert k <= len(subsetVector)
    return z3.And( z3.AtLeast(*subsetVector.value, k)
                 , z3.AtMost(*subsetVector.value , k)
                 )

  @staticmethod
  def hasAtLeastKelements(subsetVector, k):
    assert k <= len(subsetVector)
    return z3.AtLeast(*subsetVector.value, k)

  @staticmethod
  def hasAtMostKelements(subsetVector, k):
    assert k <= len(subsetVector)
    return z3.AtMost(*subsetVector.value, k)

  @staticmethod
  def isUniverse(subsetVector):
    return z3.And([v
                   for v in subsetVector.value])

  @staticmethod
  def ensureValidCombo(subsetVector, symbolicFVs):
    ensureSameLength(subsetVector, symbolicFVs)
    ensureOrdered(subsetVector.value)
    ensureOrdered(symbolicFVs)

  @staticmethod
  def interpretation(symbolicFV, subsetVector, symbolicFVs):
    return SymbolicFV.interpretation(symbolicFV, subsetVector, symbolicFVs)

  @staticmethod
  def describes(subsetVector, subset, orderedObjects):
    ensureSameLength(subsetVector, orderedObjects)
    assert len(subset) <= len(orderedObjects)
    numObjects = len(orderedObjects)
    return z3.And([v == orderedObjects[i] in subset
                   for i,v in enumerate(subsetVector.value)])

  @staticmethod
  def eq(subsetVectorLeft, subsetVectorRight):
    ensureSameLength(subsetVectorLeft, subsetVectorRight)
    assert type(subsetVectorLeft)  == SymbolicSubsetVector or type(subsetVectorLeft)  == FeatureVector
    assert type(subsetVectorRight) == SymbolicSubsetVector or type(subsetVectorRight) == FeatureVector
    if type(subsetVectorLeft) == FeatureVector and type(subsetVectorRight) == FeatureVector:
      return subsetVectorLeft == subsetVectorRight

    return z3.And([l == r
                     for l,r in zip(subsetVectorLeft.value, subsetVectorRight.value)])

  @staticmethod
  def neq(subsetVectorLeft, subsetVectorRight):
    # THIS IS NOT WHAT neq SHOULD BE - it should be like 'complementary' below except with disjunction
    # FIXME check callsites and any tests dependent on this
    return SymbolicSubsetVector.complementary(subsetVectorLeft, subsetVectorRight)

  @staticmethod
  def complementary(subsetVectorLeft, subsetVectorRight):
    return z3.And([l != r
                   for l,r in zip(subsetVectorLeft, subsetVectorRight)])

  # @staticmethod
  # def distinctFrom(subsetVectors, subsetVector):
  #   pass

  @staticmethod
  def isSubseteq(subsetVectorLeft, subsetVectorRight):
    ensureSameLength(subsetVectorLeft, subsetVectorRight)
    return z3.And([z3.Implies(l, l == r)
                   for l,r in zip(subsetVectorLeft.value, subsetVectorRight.value)])

  @staticmethod
  def isSupseteq(subsetVectorLeft, subsetVectorRight):
    return SymbolicSubsetVector.isSubseteq(subsetVectorRight,subsetVectorLeft)

  @staticmethod
  def intersection(subsetVectorLeft, subsetVectorRight, subsetIntersect):
    return z3.And([i == z3.And(l,r)
                   for l,r,i in zip(subsetVectorLeft,
                                    subsetVectorRight,
                                    subsetIntersect)])

  @staticmethod
  def union(subsetVectorLeft, subsetVectorRight, subsetUnion):
    return z3.And([u == z3.Or(l,r)
                   for l,r,u in zip(subsetVectorLeft,
                                    subsetVectorRight,
                                    subsetUnion)])

  @staticmethod
  def difference(subsetVectorLeft, subsetVectorRight, subsetDifference):
    return z3.And([d == z3.And(l,z3.Not(r))
                   for l,r,d in zip(subsetVectorLeft,
                                    subsetVectorRight,
                                    subsetDifference)])




@dataclass
class SymbolicFV:
  defined: tuple
  valence: tuple

  def unwrap(self):
    return self.defined, self.valence

  @staticmethod
  def unwraps(outType=None):
    def f(symbolicFVs):
      pairs = tuple(map(lambda s: s.unwrap(), symbolicFVs))
      defineds, valences = tuple(map(fst, pairs)), tuple(map(snd, pairs))
      if outType is None or outType == tuple:
        return defineds, valences
      else:
        return outType(defineds), outType(valences)
    return f

  def ensureValidity(self):
    ensureSameLength(self.defined, self.valence)
    ensureOrdered(self.defined)
    ensureOrdered(self.valence)

  def __len__(self) -> int:
    self.ensureValidity()
    return len(self.defined)

  def numFeatures(self) -> int:
    return len(self.defined)

  @staticmethod
  def mk(numFeatures: int, identifier: str):
    return SymbolicFV([z3.Bool(f"def_{identifier}_{j}") for j in range(numFeatures)],
                      [z3.Bool(f"val_{identifier}_{j}") for j in range(numFeatures)])

  @staticmethod
  def mks(numFeatures: int, identifier, numVectors: int):
    if type(identifier) == str:
      return tuple([SymbolicFV.mk(numFeatures, f"{identifier}_{k}") for k in range(numVectors)])
    else:
      return tuple([SymbolicFV.mk(numFeatures, identifier[k]      ) for k in  range(numVectors)])

  @staticmethod
  def mkFromConcreteFV(concreteFV, identifier):
    numFeatures  = len(concreteFV)
    symbolicFV   = SymbolicFV.mk(numFeatures, identifer)
    eqConstraint = SymbolicFV.eq(symbolicFV, concreteFV)
    return symbolicFV, eqConstraint

  @staticmethod
  def mkFromConcreteFVs(concreteFVs, identifier):
    ensureSameLengths(concreteFVs)
    numVectors    = len(concreteFVs)
    numFeatures   = len(concreteFVs[0])
    symbolicFVs   = SymbolicFV.mks(numFeatures, identifier, numVectors)
    eqConstraints = SymbolicFV.eq4(symbolicFVs, concreteFVs)
    return symbolicFVs, eqConstraints

  @staticmethod
  def eq(symbolicFV_left, symbolicFV_right):
    ensureSameLength(symbolicFV_left, symbolicFV_right)
    numFeatures = len(symbolicFV_left)
    if type(symbolicFV_left) == SymbolicFV:
      # print(f"SymbolicFV_left :: '{type(symbolicFV_left)}' (?=? SymbolicFV)")
      defined_left , valence_left  =  symbolicFV_left.defined, symbolicFV_left.valence
    elif type(symbolicFV_left) == FeatureVector:
      # print(f"SymbolicFV_left :: '{type(symbolicFV_left)}' (?=? FeatureVector)")
      defined_left , valence_left  =  symbolicFV_left.toBooleans()
    else:
      raise Exception(f"unknown type {type(symbolicFV_left)}")
    if type(symbolicFV_right) == SymbolicFV:
      # print(f"SymbolicFV_right :: '{type(symbolicFV_right)}' (?=? SymbolicFV)")
      defined_right , valence_right  =  symbolicFV_right.defined, symbolicFV_right.valence
    elif type(symbolicFV_right) == FeatureVector:
      # print(f"SymbolicFV_right :: '{type(symbolicFV_right)}' (?=? FeatureVector)")
      defined_right , valence_right  =  symbolicFV_right.toBooleans()
    else:
      raise Exception(f"unknown type {type(symbolicFV_right)}")

    # left == right iff for every feature j,
    #  left is defined at j iff right is defined at j
    #  if left  is defined at j, left and right have the same valence at j
    # (if right is defined at j, right and left have the same valence at j)
    return z3.And([z3.And([defined_left[j] == defined_right[j],
                          z3.Implies(defined_left[j],
                                     valence_left[j] == valence_right[j]),
                          z3.Implies(defined_right[j],
                                     valence_right[j] == valence_left[j])])
                   for j in range(numFeatures)])

  @staticmethod
  def eq1(symbolicFVs):
    return SymbolicFV.eqFold(symbolicFVs)

  @staticmethod
  def eqFold(symbolicFVs):
    defineds, valences = SymbolicFV.unwraps(tuple)(symbolicFVs)
    assert len(defineds) == len(valences)
    numVectors  = len(defineds)
    numFeatures = len(defineds[0])

    return z3.And([z3.And([ defineds[0][j] == defineds[i][j]
                          , z3.Implies(defineds[0][j], valences[0][j] == valences[i][j])
                          , z3.Implies(defineds[i][j], valences[i][j] == valences[0][j])])
                   for i in range(numVectors) for j in range(numFeatures)])

  @staticmethod
  def eq2(symbolicFVs, symbolicFV):
    ensureSameLengths(symbolicFVs)
    ensureSameLength( symbolicFVs[0], symbolicFV)
    numVectors = len(symbolicFVs)
    return z3.And([SymbolicFV.eq(symbolicFVs[i], symbolicFV)
                   for i in range(numVectors)])

  @staticmethod
  def eq3(symbolicFVs, symbolicFV):
    ensureSameLengths(symbolicFVs)
    ensureSameLength( symbolicFVs[0], symbolicFV)
    numVectors = len(symbolicFVs)
    return z3.Or([SymbolicFV.eq(symbolicFVs[i], symbolicFV)
                  for i in range(numVectors)])

  @staticmethod
  def elementOf(symbolicFVs, symbolicFV):
    return SymbolicFV.eq3(symbolicFVs, symbolicFV)

  @staticmethod
  def inStack(symbolicFVs, symbolicFV):
    return SymbolicFV.eq3(symbolicFVs, symbolicFV)

  @staticmethod
  def eq4(symbolicFVs_left, symbolicFVs_right):
    ensureSameLength( symbolicFVs_left , symbolicFVs_right)
    ensureSameLengths(symbolicFVs_left )
    ensureSameLengths(symbolicFVs_right)
    numVectors = len(symbolicFVs_left)
    return z3.And([l == r
                   for l,r in zip( symbolicFVs_left
                                 , symbolicFVs_right
                                 )
                  ])

  @staticmethod
  def eqVectorsEqOrder(symbolicFVs_left, symbolicFVs_right):
    return SymbolicFV.eq4(symbolicFVs_left, symbolicFVs_right)

  @staticmethod
  def eq5(symbolicFVs_left, symbolicFVs_right):
    ensureSameLength( symbolicFVs_left , symbolicFVs_right)
    ensureSameLengths(symbolicFVs_left )
    ensureSameLengths(symbolicFVs_right)
    numVectors = len(symbolicFVs_left)
    return z3.And([ z3.And([ SymbolicFV.eq3( symbolicFVs_right
                                           , symbolicFVs_left[k]
                                           )
                             for k in range(numVectors)
                           ])
                  , z3.And([ SymbolicFV.eq3( symbolicFVs_left
                                           , symbolicFVs_right[k]
                                           )
                             for k in range(numVectors)
                           ])
                  ])

  @staticmethod
  def isSubsetEq(symbolicFVs_left, symbolicFVs_right):
    ensureSameLength(  symbolicFVs_left[0]
                    , symbolicFVs_right[0]
                    )
    ensureSameLengths(symbolicFVs_left )
    ensureSameLengths(symbolicFVs_right)
    numInSubset = len(symbolicFVs_left)
    numObjects  = symbolicFVs_right
    return z3.And([ SymbolicFV.eq3( symbolicFVs_right
                                  , symbolicFVs_left[k]
                                  )
                    for k in range(numInSubset)
                  ])

  @staticmethod
  def isSupersetEq(symbolicFVs_left, symbolicFVs_right):
    return SymbolicFV.isSubsetEq(symbolicFVs_left, symbolicFVs_right)


  @staticmethod
  def neq(symbolicFV_left, symbolicFV_right):
    return SymbolicFV.distinct(symbolicFV_left, symbolicFV_right)

  @staticmethod
  def distinct(symbolicFV_left, symbolicFV_right):
    return z3.Not(SymbolicFV.eq(symbolicFV_left, symbolicFV_right))

  @staticmethod
  def nonZero(symbolicFV):
    numFeatures = len(symbolicFV)
    return z3.Or([symbolicFV.defined[j]
                  for j in range(numFeatures)])

  @staticmethod
  def fullySpecified(symbolicFV):
    numFeatures = len(symbolicFV)
    return z3.And([symbolicFV.defined[j]
                   for j in range(numFeatures)])

  @staticmethod
  def pairwise_neq1(symbolicFVs):
    return SymbolicFV.pairwise_distinct1(symbolicFVs)

  @staticmethod
  def pairwise_distinct1(symbolicFVs):
    defineds, valences = SymbolicFV.unwraps(tuple)(symbolicFVs)
    assert len(defineds) == len(valences)
    numVectors  = len(defineds)
    numFeatures = len(defineds[0])

    #the stack of vectors is pairwise distinct iff forall vectors i,k
    # Either
    #  i == k
    # or
    # for at least one feature j, either
    #    1. i is defined at j but k isn't (or vice versa)
    #    2. both i and k are defined at j and have different valences
    return z3.And([z3.Or([ z3.Or([          defineds[i][j] != defineds[k][j]
                                 , z3.And([ defineds[i][j]
                                          , defineds[k][j]
                                          , valences[i][j] != valences[k][j]
                                          ])
                                 ])
                          for j in range(numFeatures)])
                   for i,k in product(range(numVectors), range(numVectors))
                   if i != k
                  ])

  @staticmethod
  def isCoveredBy(symbolicFV_left, symbolicFV_right):
    ensureSameLengths(symbolicFV_left, symbolicFV_right)
    numFeatures = len(symbolicFV_left)
    x = SymbolicFV.mk(numFeatures, "x") # auxiliary variable used in universally quantified formula below
    #  l isCoveredBy r
    # holds iff
    #  1. l <= r
    #  2. there is no x \neq r s.t. l <= x <= r
    #   == for every x, it is not the case that
    #     l <= x <= r \land x \neq r
    return z3.And( SymbolicFV.le(symbolicFV_left, symbolicFV_right)
                 , z3.ForAll(x
                            , z3.Not(z3.And([ SymbolicFV.le( l, x)
                                            , SymbolicFV.le( x, r)
                                            , SymbolicFV.neq(x, r)
                                            ]))
                             )
                 )

  @staticmethod
  def covers(symbolicFV_left, symbolicFV_right):
    return SymbolicFV.isCoveredBy(symbolicFV_right, symbolicFV_left)

  @staticmethod
  def between(symbolicFV_lb, symbolicFV, symbolicFV_ub):
    return z3.And( SymbolicFV.le(symbolicFV_lb, symbolicFV   )
                 , SymbolicFV.le(symbolicFV   , symbolicFV_ub)
                 )

  # @staticmethod
  # def lt(symbolicFV_left, symbolicFV_right):
  #   pass

  # @staticmethod
  # def lt1(symbolicFVs, lowerBound):
  #   pass

  @staticmethod
  def le(symbolicFV_left, symbolicFV_right):
    ensureSameLength(symbolicFV_left, symbolicFV_right)
    defined_left , valence_left  = symbolicFV_left.unwrap()
    defined_right, valence_right = symbolicFV_right.unwrap()
    numFeatures = len(symbolicFV_left)
    # left <= right iff for every feature j, one of the following holds:
    #  - both left and right are   defined at j and have the same valence
    #  - both left and right are undefined at j
    #  - left is *un*defined at j and right is *defined* at j
    # Recall: the unique minimal element is defined *nowhere*
    return z3.And([z3.Or([z3.And([defined_left[j], defined_right[j], valence_left[j] == valence_right[j]]),
                          z3.And(z3.Not(defined_left[j]), z3.Not(defined_right[j])),
                          z3.And(z3.Not(defined_left[j]), defined_right[j])])
                   for j in range(numFeatures)])

  @staticmethod
  def le1(symbolicFVs, lowerBound):
    defineds, valences = SymbolicFV.unwraps(tuple)(symbolicFVs)
    defined_lowerBound, valence_lowerBound = lowerBound.unwrap()
    numVectors  = len(defineds)
    assert len(lowerBound) == len(defineds[0])
    numFeatures = len(lowerBound)

    return z3.And([z3.Or([ z3.And([defined_lowerBound[j], defineds[i][j], valence_lowerBound[j] == valences[i][j]])
                         , z3.And(z3.Not(defined_lowerBound[j]), z3.Not(defineds[i][j]))
                         , z3.And(z3.Not(defined_lowerBound[j]), defineds[i][j])
                         ])
                   for i in range(numVectors) for j in range(numFeatures)])

  @staticmethod
  def ge(symbolicFV_left, symbolicFV_right):
    ensureSameLength(symbolicFV_left, symbolicFV_right)
    return SymbolicFV.le(symbolicFV_left, symbolicFV_right)

  @staticmethod
  def ge1(symbolicFVs, upperBound):
    defineds, valences = SymbolicFV.unwraps(tuple)(symbolicFVs)
    defined_upperBound, valence_upperBound = upperBound.unwrap()
    numVectors  = len(defineds)
    assert len(upperBound) == len(defineds[0])
    numFeatures = len(upperBound)

    return z3.And([z3.Or([ z3.And([defineds[i][j], defined_upperBound[j], valences[i][j] == valence_upperBound[j]])
                         , z3.And(z3.Not(defineds[i][j]), z3.Not(defined_upperBound[j]))
                         , z3.And(z3.Not(defineds[i][j]), defined_upperBound[j])
                         ])
                   for i in range(numVectors) for j in range(numFeatures)])

  # @staticmethod
  # def gt(symbolicFV_left, symbolicFV_right):
  #   pass

  # @staticmethod
  # def gt1(symbolicFVs, upperBound):
  #   pass

  @staticmethod
  def comparable(symbolicFV_left, symbolicFV_right):
    ensureSameLength(symbolicFV_left, symbolicFV_right)
    defined_left , valence_left  = symbolicFV_left.unwrap()
    defined_right, valence_right = symbolicFV_right.unwrap()
    return z3.Or(le( defined_left,  valence_left, defined_right, valence_right),
                 le(defined_right, valence_right,  defined_left,  valence_left))

  @staticmethod
  #pairwise comparability
  def comparable1(symbolicFVs):
    defineds, valences = SymbolicFV.unwraps(tuple)(symbolicFVs)
    return z3.And([comparable(a[0], a[1], b[0], b[1])
                   for a,b in product(zip(defineds, valences),
                                      zip(defineds, valences))])

  @staticmethod
  def meet(symbolicFV_left, symbolicFV_right, meet):
    ensureSameLength(symbolicFV_left, symbolicFV_right)
    ensureSameLength(symbolicFV_left, meet)
    defined_left , valence_left  = symbolicFV_left.unwrap()
    defined_right, valence_right = symbolicFV_right.unwrap()
    defined_meet , valence_meet  = meet.unwrap()
    numFeatures = len(symbolicFV_left)
    return z3.And([z3.And([defined_meet[j] == z3.And([defined_left[j], defined_right[j], valence_left[j] == valence_right[j]]),
                           z3.Implies(defined_meet[j], z3.And([valence_meet[j] == valence_left[j],
                                                               valence_meet[j] == valence_right[j]]))])
                   for j in range(numFeatures)])

  @staticmethod
  def meet1(symbolicFVs, meet):
    defineds, valences = SymbolicFV.unwraps(tuple)(symbolicFVs)
    defined_meet, valence_meet = meet.unwrap()
    assert len(meet) == len(defineds[0])
    numObjects  = len(defineds)
    numFeatures = len(meet)

    allDefinedAtJandTrue  = lambda j: z3.And([z3.And(defineds[i][j],        valences[i][j])  for i in range(numObjects)])
    allDefinedAtJandFalse = lambda j: z3.And([z3.And(defineds[i][j], z3.Not(valences[i][j])) for i in range(numObjects)])
    allDefinedAtJAndSame  = lambda j: z3.Or([allDefinedAtJandTrue(j), allDefinedAtJandFalse(j)])
    meetDefinedAtJ        = lambda j: allDefinedAtJAndSame(j)
    meetTrueAtJ           = lambda j: allDefinedAtJandTrue(j)
    meetFalseAtJ          = lambda j: allDefinedAtJandFalse(j)

    return z3.And([z3.And([ defined_meet[j] == meetDefinedAtJ(j)
                          , z3.Implies(meetTrueAtJ( j),        valence_meet[j] )
                          , z3.Implies(meetFalseAtJ(j), z3.Not(valence_meet[j]))
                          ])
                   for j in range(numFeatures)])

  @staticmethod
  def meet2(symbolicFVs, symbolicSubsetVec, meet):
    defineds, valences = SymbolicFV.unwraps(tuple)(symbolicFVs)
    defined_meet, valence_meet = meet.unwrap()
    assert len(meet) == len(defineds[0])
    numObjects  = len(defineds)
    numFeatures = len(meet)

    subsetVec = symbolicSubsetVec.value

    allDefinedAtJandTrue  = lambda j: z3.And([ z3.Implies( subsetVec[i]
                                                         , z3.And(defineds[i][j],        valences[i][j])
                                            )
                                             for i in range(numObjects)])
    allDefinedAtJandFalse = lambda j: z3.And([ z3.Implies( subsetVec[i]
                                                         , z3.And(defineds[i][j], z3.Not(valences[i][j]))
                                                         )
                                              for i in range(numObjects)])
    allDefinedAtJAndSame  = lambda j: z3.Or([allDefinedAtJandTrue(j), allDefinedAtJandFalse(j)])
    meetDefinedAtJ        = lambda j: allDefinedAtJAndSame(j)
    meetTrueAtJ           = lambda j: allDefinedAtJandTrue(j)
    meetFalseAtJ          = lambda j: allDefinedAtJandFalse(j)

    return z3.And([z3.And([ defined_meet[j] == meetDefinedAtJ(j)
                          , z3.Implies(meetTrueAtJ( j),        valence_meet[j] )
                          , z3.Implies(meetFalseAtJ(j), z3.Not(valence_meet[j]))
                          ])
                   for j in range(numFeatures)])

  @staticmethod
  def joinable(symbolicFV_left, symbolicFV_right):
    ensureSameLength(symbolicFV_left, symbolicFV_right)
    defined_left , valence_left  = symbolicFV_left.unwrap()
    defined_right, valence_right = symbolicFV_right.unwrap()
    numFeatures = len(symbolicFV_left)
    # left \lor right exists iff for all features j
    #  Either
    #   1.      def_l[j] \land      def_r[j] \land val_l[j] == val_r[j]
    #   2. \neg def_l[j]
    #   3. \neg def_r[j]
    return z3.And([z3.Or([ z3.And([defined_left[j], defined_right[j], valence_left[j] == valence_right[j]])
                         , z3.Not(defined_left[j])
                         , z3.Not(defined_right[j])
                         ])
                   for j in range(numFeatures)])

  @staticmethod
  def joinable1(symbolicFVs):
    defineds, valences = SymbolicFV.unwraps(tuple)(symbolicFVs)
    numObjects  = len(defineds)
    numFeatures = len(defineds[0])

    atLeastOneDefinedAtJAndTrue  = lambda j: z3.Or([z3.And(        defineds[i][j]
                                                     ,        valences[i][j]
                                                     )
                                                    for i in range(numObjects)])
    atLeastOneDefinedAtJAndFalse = lambda j: z3.Or([z3.And(        defineds[i][j]
                                                     , z3.Not(valences[i][j])
                                                     )
                                                    for i in range(numObjects)])
    noConflictsAtJ               = lambda j: z3.Not(z3.And( atLeastOneDefinedAtJAndTrue(j)
                                                     , atLeastOneDefinedAtJAndFalse(j)
                                                     ))
    return z3.And([noConflictsAtJ(j)
                   for j in range(numFeatures)])

  @staticmethod
  def join(symbolicFV_left, symbolicFV_right, join):
    ensureSameLength(symbolicFV_left, symbolicFV_right)
    ensureSameLength(symbolicFV_left, join)
    defined_left , valence_left  = symbolicFV_left.unwrap()
    defined_right, valence_right = symbolicFV_right.unwrap()
    defined_join , valence_join  = join.unwrap()
    numFeatures = len(symbolicFV_left)

    assert len(defined_right) == len(valence_right)
    assert len(defined_left)  == len(defined_right)
    numFeatures = len(defined_left)

    exactlyOneDefinedAtJ         = lambda j: z3.Xor(            defined_left[j]
                                                   ,            defined_right[j]
                                                   )
    exactlyOneDefinedAndTrueAtJ  = lambda j: z3.Xor(  z3.And(         defined_left[j]
                                                            ,         valence_left[j])
                                                   ,  z3.And(        defined_right[j]
                                                            ,        valence_right[j])
                                                   )
    exactlyOneDefinedAndFalseAtJ = lambda j: z3.Xor(  z3.And(        defined_left[j]
                                                            , z3.Not(valence_left[j]))
                                                   ,  z3.And(        defined_right[j]
                                                            , z3.Not(valence_right[j]))
                                                   )

    bothDefinedAndTrueAtJ        = lambda j: z3.And([        defined_left[j] ,        defined_right[j],
                                                             valence_left[j] ,        valence_right[j]])
    bothDefinedAndFalseAtJ       = lambda j: z3.And([        defined_left[j] ,        defined_right[j],
                                                      z3.Not(valence_left[j]), z3.Not(valence_right[j])])
    bothDefinedAndSameAtJ        = lambda j: z3.Or(bothDefinedAndTrueAtJ(j)  , bothDefinedAndFalseAtJ(j))


    return z3.And([ SymbolicFV.joinable(symbolicFV_left, symbolicFV_right)
                  ] +
                  [z3.And([        defined_join[j]  == z3.Or([ bothDefinedAndSameAtJ(j)
                                                             , exactlyOneDefinedAtJ(j)])
  #                         ,        valence_join[j]  == z3.Or( bothDefinedAndTrueAtJ(j)
  #                                                           , exactlyOneDefinedAndTrueAtJ(j))
  #                         , z3.Not(valence_join[j]) == z3.Or( bothDefinedAndFalseAtJ(j)
  #                                                           , exactlyOneDefinedAndFalseAtJ(j))
                          , z3.Implies( z3.Or( bothDefinedAndTrueAtJ(j)
                                             , exactlyOneDefinedAndTrueAtJ(j))
                                      ,        valence_join[j]
                                      )
                          , z3.Implies( z3.Or( bothDefinedAndFalseAtJ(j)
                                             , exactlyOneDefinedAndFalseAtJ(j))
                                      , z3.Not(valence_join[j])
                                      )
                          ])
                   for j in range(numFeatures)])

  @staticmethod
  def join1(defineds, valences, join):
    defineds, valences = SymbolicFV.unwraps(tuple)(symbolicFVs)
    defined_join, valence_join = join.unwrap()
    assert len(join) == len(defineds[0])
    numObjects  = len(defineds)
    numFeatures = len(join)

    atLeastOneDefinedAtJAndTrue  = lambda j: z3.Or([z3.And(        defineds[i][j]
                                                          ,        valences[i][j]
                                                          )
                                                    for i in range(numObjects)])
    atLeastOneDefinedAtJAndFalse = lambda j: z3.Or([z3.And(        defineds[i][j]
                                                          , z3.Not(valences[i][j])
                                                          )
                                                    for i in range(numObjects)])
    joinIsDefinedAtJ         = lambda j: z3.Xor( atLeastOneDefinedAtJAndTrue(j)
                                               , atLeastOneDefinedAtJAndFalse(j)
                                               )
    joinIsDefinedAtJAndTrue  = lambda j: z3.And( joinIsDefinedAtJ(j)
                                               , atLeastOneDefinedAtJAndTrue(j)
                                               )
    joinIsDefinedAtJAndFalse = lambda j: z3.And( joinIsDefinedAtJ(j)
                                               , atLeastOneDefinedAtJAndFalse(j)
                                               )
    return z3.And([z3.And([ SymbolicFV.joinable1(defineds, valences)
                          , defined_join[j] == joinIsDefinedAtJ(j)
                          , z3.Implies( joinIsDefinedAtJAndTrue(j)
                                      , valence_join[j]
                                      )
                          , z3.Implies( joinIsDefinedAtJAndFalse(j)
                                      , z3.Not(valence_join[j])
                                      )
                          ])
                   for j in range(numFeatures)])

  @staticmethod
  def interpretation(symbolicFV, symbolicSubsetVec, symbolicFVs):
    ensureSameLength(symbolicSubsetVec, symbolicFVs)
    numObjects = len(symbolicFVs)
    return z3.And([ symbolicSubsetVec.value[i] == SymbolicFV.le( symbolicFV
                                                               , symbolicFVs[i]
                                                               )
                    for i in range(numObjects)])

  @staticmethod
  def interpretation1(symbolicFV, symbolicFVs_subset, symbolicFVs_objects):
    ensureSameLength(symbolicFV, symbolicFVs_subset[0])
    ensureSameLength(symbolicFV, symbolicFVs_objects[0])
    ensureSameLengths(symbolicFVs_subset)
    ensureSameLengths(symbolicFVs_objects)
    numObjects  = len(symbolicFVs_objects)
    numInSubset = len(symbolicFVs_subset)
    numFeatures = len(symbolicFV)
    # asserts that for every object i in the set of objects,
    #   symbolicFV <= object i  iff object i is equal to some object in the subset
    # asserts that for every object k in the subset,
    #   symbolicFV <= object k \land object k is equal to some object in the subset
    return z3.And( z3.And([ SymbolicFV.le(  symbolicFV
                                         ,  symbolicFVs_objects[i]) == \
                            SymbolicFV.eq3( symbolicFVs_subset
                                          , symbolicFVs_objects[i]
                                          )
                            for i in range(numObjects)
                          ])
                 , z3.And([ z3.And([ SymbolicFV.le( symbolicFV
                                                  , symbolicFVs_subset[k]
                                                  )
                                   , SymbolicFV.eq3( symbolicFVs_objects
                                                   , symbolicFVs_subset[k]
                                                   )
                                   ])
                            for k in range(numInSubset)
                          ])
                 )

  @staticmethod
  def synonyms(symbolicFV_left, symbolicFV_right, symbolicFVs):
    ensureSameLength(symbolicFV_left, symbolicFV_right)
    ensureSameLengths(symbolicFVs)
    ensureSameLength(symbolicFV_left, symbolicFVs[0])
    numObjects   = len(symbolicFVs)
    numFeatures  = len(symbolicFV_left)
    interp_left  = SymbolicFV.mk(numFeatures, "interp_left")
    interp_right = SymbolicFV.mk(numFeatures, "interp_right")
    # interp_left  is the interpretation of symbolicFV_left  relative to the stack
    # interp_right is the interpretation of symbolicFV_right relative to the stack
    # interp_left and interp_right are the same
    return z3.And([ SymbolicFV.interpretation(symbolicFV_left , interp_left , symbolicFVs)
                  , SymbolicFV.interpretation(symbolicFV_right, interp_right, symbolicFVs)
                  , SymbolicSubsetVector.eq(interp_left, interp_right)
                  ])

  @staticmethod
  def synonyms1(symbolicFVs_synonyms, symbolicFVs_objects):
    ensureSameLength( symbolicFVs_synonyms    )
    ensureSameLength( symbolicFVs_objects     )
    ensureSameLength( symbolicFVs_synonyms[0]
                    ,  symbolicFVs_objects[0]
                    )
    numSynonyms = len(symbolicFVs_synonyms    )
    numObjects  = len(symbolicFVs_objects     )
    return z3.And([ SymbolicFV.synonyms( symbolicFVs_synonyms[0]
                                       , symbolicFVs_synonyms[k]
                                       , symbolicFVs_objects
                                       )
                    for k in range(numSynonyms)
                  ])

  # universal quantifier might be worth avoiding? I don't really know / haven't tried to test that idea yet
  # using allSmt is also an option but with different trade-offs (e.g. answer set size could be enormous)
  @staticmethod
  def synonymClosure(symbolicFVs_synonyms, symbolicFV, symbolicFVs_objects):
    ensureSameLength( symbolicFVs_synonyms     )
    ensureSameLength( symbolicFVs_objects      )
    ensureSameLength( symbolicFVs_synonyms[0]
                    ,  symbolicFVs_objects[0]
                    )
    ensureSameLength( symbolicFVs_synonyms[0]
                    , symbolicFV
                    )
    numSynonyms  = len(symbolicFVs_synonyms    )
    numObjects   = len(symbolicFVs_objects     )
    numFeatures  = len(symbolicFV)
    x            = SymbolicFV.mk(numFeatures, "x") # auxiliary var for use in quantified formula below
    #               First two conjuncts here are redundant with the third
    return z3.And([ SymbolicFV.eq3(symbolicFVs_synonyms, symbolicFV)
                  , SymbolicFV.synonyms1(symbolicFVs_synonyms, symbolicFVs_objects)
                  , z3.ForAll( x
                               , SymbolicFV.synonyms( x
                                                    , symbolicFV
                                                    , symbolicFVs_objects
                                                    ) == \
                                 SymbolicFV.eq3(symbolicFVs_synonyms, x)
                             )
                  ])

  @staticmethod
  def naturalClasses(symbolicFVs_nc, symbolicFVs_subset, symbolicFVs_object):
    ensureSameLengths(symbolicFVs_nc)
    ensureSameLengths(symbolicFVs_subset)
    ensureSameLengths(symbolicFVs_object)
    ensureSameLength(symbolicFVs_nc[0], symbolicFVs_subset[0])
    ensureSameLength(symbolicFVs_nc[0], symbolicFVs_object[0])
    numNaturalClasses = len(symbolicFVs_nc)
    numInSubset       = len(symbolicFVs_subset)
    numObjects        = len(symbolicFVs_object)
    numFeatures       = len(symbolicFVs_nc[0])

    meet = SymbolicFV.mk(numFeatures, "meet")
    # \forall x, x \in symbolicFVs_nc iff x \in synonymClosure of the meet of symbolicFVs_subset
    x = SymbolicFV.mk(numFeatures)
    return z3.And( SymbolicFV.meet1( symbolicFVs_subset
                                   , meet
                                   )
                 , SymbolicFV.synonymClosure(symbolicFVs_nc, meet, symbolicFVs_object)
                 )

  @staticmethod
  def naturalClasses1(symbolicFVs_nc, symbolicSubsetVector, symbolicFVs_object):
    #length boilerplate
    # can't calculate subset length
    # can't construct symbolic subset
    # construct meet by reusing code for doing this? (shouldn't there be a meet version for this type signature?)
    pass #FIXME

  @staticmethod
  def findNaturalClasssesFor(concreteFVs_subset, concreteFVs_objects):
    ensureSameLengths(concreteFVs_subset)
    ensureSameLengths(concreteFVs_objects)
    ensureSameLength(concreteFVs_subset[0], concreteFVs_objects[0])
    numInSubset = len(concreteFVs_subset)
    numObjects  = len(concreteFVs_objects)
    numFeatures = len(concreteFVs_subset[0])

    pass #FIXME

  @staticmethod
  def findNaturalClasssesFor1(concreteSubsetVector, concreteFVs_objects):
    ensureSameLength(concreteSubsetVector, concreteFVs_objects)
    ensureSameLengths(concreteFVs_objects)
    numObjects  = len(concreteFVs_objects)
    numFeatures = len(concreteFVs_objects[0])
    pass #FIXME

  @staticmethod
  def hyponym(symbolicFV_left, symbolicFV_right, symbolicFVs):
    ensureSameLength(symbolicFV_left, symbolicFV_right)
    ensureSameLengths(symbolicFVs)
    ensureSameLength(symbolicFV_left, symbolicFVs[0])
    numObjects   = len(symbolicFVs)
    numFeatures  = len(symbolicFV_left)
    interp_left  = SymbolicFV.mk(numFeatures, "interp_left")
    interp_right = SymbolicFV.mk(numFeatures, "interp_right")
    # interp_left  is the interpretation of symbolicFV_left  relative to the stack
    # interp_right is the interpretation of symbolicFV_right relative to the stack
    # everything in interp_left is included in interp_right
    return z3.And([ SymbolicFV.interpretation(symbolicFV_left , interp_left , symbolicFVs)
                  , SymbolicFV.interpretation(symbolicFV_right, interp_right, symbolicFVs)
                  , z3.And([ z3.Implies(  interp_left.value[i]
                                       , interp_right.value[i]
                                       )
                             for i in range(numObjects)
                           ])
                  ])

  @staticmethod
  def hypernym(symbolicFV_left, symbolicFV_right, symbolicFVs):
    return SymbolicFV.hyponym(symbolicFV_right, symbolicFV_left, symbolicFVs)

  @staticmethod
  def comparableInterpretation(symbolicFV_left, symbolicFV_right, symbolicFVs):
    return z3.Or(  SymbolicFV.hyponym(symbolicFV_right, symbolicFV_left, symbolicFVs)
                , SymbolicFV.hypernym(symbolicFV_right, symbolicFV_left, symbolicFVs)
                )

  def concrete(self, model):
    return self.toConcreteFeatureVector(model)

  #Takes a model containing valuations for the symbolic booleans in defined and valence
  # and returns two tuples of concrete Booleans that define a unique FeatureVector
  def toConcreteBooleans(self, model):
     return (tuple(model[self.defined[i]] for i in range(len(self))),
             tuple(model[self.valence[i]] for i in range(len(self))))


  # Takes a model containing valuations for the symbolic booleans in defined and valence
  # and returns the corresponding concrete FeatureVector
  def toConcreteFeatureVector(self, model):
     concrete_defined, concrete_valence = self.toConcreteBooleans(model)
     return FeatureVector.fromBooleans(concrete_defined, concrete_valence)

  @staticmethod
  def toConcreteBooleans1(symbolicFVs, model):
    return lmap(lambda s: s.toConcreteBooleans(model), symbolicFVs)

  @staticmethod
  def toConcreteFeatureVectors(symbolicFVs, model):
    return lmap(lambda s: s.toConcreteFeatureVector(model), symbolicFVs)

  @staticmethod
  def toConcreteFeatureVector1(symbolicFVs, model):
    return SymbolicFV.toConcreteFeatureVectors(symbolicFVs, model)

  @staticmethod
  def concrete1(symbolicFVs, model):
    return SymbolicFV.toConcreteFeatureVectors(symbolicFVs, model)
