from typing import Optional, Callable
from typing import Set

import hypothesis
from hypothesis import given
from hypothesis import strategies as st
from hypothesis.strategies import SearchStrategy

import z3

import saguaro.utilities as SU
import saguaro._Boolean as SB

from saguaro._Boolean import Bool \
                           , id_Bool \
                           , bool_to_BoolRef1
from saguaro._Boolean import Not, Not1 \
                           , And, And1 \
                           , Or, Or1 \
                           , Implies, Implies1 \
                           , Iff, Iff1 \
                           , _strategy_bool, _strategy_BoolRef

def test_should_pass():
  assert False == False

# def test_should_fail():
#   assert False == True


# Goal of "basic" tests is simply to check that every call of
# every type signature expected is defined and has the expected type

def test_Boolean_implementations_type_basic():
  # extremely low priority TODO: break up and exhaust test coverage
  # this is semi-random coverage to start
  assert type(SB.Not(           SB.Not(True))) == bool
  assert type(SB.Not(           z3.Not(True))) == z3.BoolRef
  assert type(SB.And(      True, SB.Not(True))) == bool
  assert type(SB.And(      True, z3.Not(True))) == z3.BoolRef
  assert type(SB.Or(       True, SB.Not(True))) == bool
  assert type(SB.Or(       True, z3.Not(True))) == bool
  assert type(SB.Implies(  True, SB.Not(True))) == bool
  assert type(SB.Implies(  True, z3.Not(True))) == z3.BoolRef
  assert type(SB.Iff(      True, SB.Not(True))) == bool
  assert type(SB.Iff(      True, z3.Not(True))) == z3.BoolRef

  assert type(SB.Not1([     True, SB.Not(True)])) == bool
  assert type(SB.Not1([     True, z3.Not(True)])) == z3.BoolRef
  assert type(SB.And1([     True, SB.Not(True)])) == bool
  assert type(SB.And1([     True, z3.Not(True)])) == z3.BoolRef
  assert type(SB.Or1([      True, SB.Not(True)])) == bool
  assert type(SB.Or1([      True, z3.Not(True)])) == z3.BoolRef
  assert type(SB.Implies1([ True,
                            True
                          ]
                          , SB.Not(True))) == bool
  assert type(SB.Implies1([ True,
                            True
                          ]
                          , z3.Not(True))) == z3.BoolRef
  assert type(SB.Iff1([    True, SB.Not(True)])) == bool
  assert type(SB.Iff1([    True, z3.Not(True)])) == z3.BoolRef


def test_Boolean_bool_values_basic():
  # very low priority TODO: break up and exhaust test coverage
  #  - there's only five functions to check
  assert SB.Not(           SB.Not(True)) == True
  assert SB.And(     True, SB.Not(True)) == False
  assert SB.Or(      True, SB.Not(True)) == True
  assert SB.Or(      True, z3.Not(True)) == True
  assert SB.Implies( True, SB.Not(True)) == False
  assert SB.Iff(     True, SB.Not(True)) == False

  assert SB.Not1([     True, SB.Not(True)]) == False
  # assert SB.Not1([     True, z3.Not(True)]) == False
  assert SB.And1([     True, SB.Not(True)]) == False
  assert SB.Or1([      True, SB.Not(True)]) == True
  # assert SB.Or1([      True, z3.Not(True)]) == True
  assert SB.Implies1([ True,
                       True
                     ]
                     , SB.Not(True)) == False
  assert SB.Iff1([    True, SB.Not(True)]) == False


# VERIFY CONCRETE IMPLEMENTATIONS AGAINST REFERENCE IMPLEMENTATION

UnaryOp_Bool = Callable[[Bool], Bool]
# UnaryOp_CollectionBool = Callable[[Collection[Bool]], Bool]
BinaryOp_Bool = Callable[[Bool, Bool], Bool]
# BinaryOp_CollectionBool_Bool = Callable[[Collection[Bool], Bool], Bool]
# BinaryOp_CollectionBool = Callable[[Collection[Bool], Collection[Bool]], Bool]

def checkImplementation_unaryOp(imp: UnaryOp_Bool, ref: UnaryOp_Bool):
  def inner(b: Bool, postProcess: Optional[UnaryOp_Bool] = None) -> bool:
    if postProcess is None and type(b) != z3.BoolRef:
      return imp(b) == ref(b)
    elif postProcess is None and type(b) == z3.BoolRef:
      return z3.simplify(imp(b)) == ref(b)
    elif postProcess is not None and type(b) == z3.BoolRef:
      LHS = z3.simplify(imp(b))
      RHS = postProcess(ref(b))
      return LHS.eq(RHS)
    else:
      raise Exception(f"{type(b)}, {postProcess}, {ref}, {imp}")
  return inner

def checkImplementation_binaryOp(imp: BinaryOp_Bool, ref: BinaryOp_Bool):
  def inner(p: Bool, q: Bool, postProcess: Optional[UnaryOp_Bool] = None) -> bool:
    if postProcess is None and type(p) != z3.BoolRef and type(q) != z3.BoolRef:
      return imp(p, q) == ref(p, q)
    elif postProcess is None and type(p) == z3.BoolRef and type(q) == z3.BoolRef:
      return z3.simplify(imp(p, q)) == ref(p, q)
    elif postProcess is not None and type(p) == z3.BoolRef and type(q) == z3.BoolRef:
      LHS = z3.simplify(imp(p, q))
      RHS = postProcess(ref(p, q))
      return LHS.eq(RHS)
    else:
      raise Exception(f"{type(p)}, {type(q)}, {postProcess}, {ref}, {imp}")
  return inner

def Not_func_referenceImplementation(b: Bool) -> Bool:
  return not b

# def Not1_func_referenceImplementation(b: Collection[Bool]) -> Bool:
#   return not b

def Not_checkImplementation(not_imp: UnaryOp_Bool):
  return checkImplementation_unaryOp(not_imp, Not_func_referenceImplementation)

# def Not1_checkImplementation(not_imp: Callable[[Collection[Bool], Bool], Bool]):

def And_func_referenceImplementation(p: bool, q: Bool) -> Bool:
  return p and q

# def And1_func_referenceImplementation(bs: Collection[Bool]) -> Bool:

def And_checkImplementation(and_imp: BinaryOp_Bool):
  return checkImplementation_binaryOp(and_imp, And_func_referenceImplementation)

# def And1_checkImplementation(and_imp: Callable[[Collection[Bool], Bool], Bool]):

def Or_func_referenceImplementation(p: bool, q: Bool) -> Bool:
  return p or q

# def Or1_func_referenceImplementation(bs: Collection[Bool]) -> Bool:

def Or_checkImplementation(or_imp: BinaryOp_Bool):
  return checkImplementation_binaryOp(or_imp, Or_func_referenceImplementation)

# def Or1_checkImplementation(or_imp: Callable[[Collection[Bool], Bool], Bool], postProcess: Optional[Callable[[bool], Bool]] = None):

def Implies_func_referenceImplementation(p: bool, q: Bool) -> Bool:
  return (not p) or q

# def Implies1_func_referenceImplementation(ps: Collection[Bool], q: Bool) -> Bool:

def Implies_checkImplementation(implies_imp: BinaryOp_Bool):
  return checkImplementation_binaryOp(implies_imp, Implies_func_referenceImplementation)

# def Implies1_checkImplementation(implies_imp: Callable[[Collection[Bool], Bool], Bool]):

def Iff_func_referenceImplementation(p: bool, q: Bool) -> Bool:
  return ((not p) or q) and ((not q) or p)

# def Iff1_func_referenceImplementation(bs: Collection[Bool]) -> Bool:

def Iff_checkImplementation(iff_imp: BinaryOp_Bool):
  return checkImplementation_binaryOp(iff_imp, Iff_func_referenceImplementation)

# def Iff1_checkImplementation(iff_imp: Callable[[Collection[Bool]], Bool]):


@given(_strategy_bool())
def test_Not_bool_check(b: bool):
  assert Not_checkImplementation(Not)(b)

#FIXME need to figure out how to idiomatically generate collections (or specify something for _Collection_Bool)
# def test_Not1_bool_check(bs: Collection[Bool]):
#   assert Not1_checkImplementation(Not1)(bs)

@given(_strategy_bool(), _strategy_bool()) #FIXME change second arg to a custom generator for Bool
def test_And_bool_check(p: bool, q: bool):
  assert And_checkImplementation(And)(p, q)

#FIXME collection
# def test_And1_bool_check(bs: Collection[Bool]):
#   assert And1_checkImplementation(And1)(b)

#FIXME second arg
@given(_strategy_bool(), _strategy_bool()) #FIXME change second arg to a custom generator for Bool
def test_Or_bool_check(p: bool, q: bool):
  assert Or_checkImplementation(Or)(p, q)

#FIXME collection
# def test_Or1_bool_check(bs: Collection[Bool]):
#   assert Or1_checkImplementation(Or1)(b)

#FIXME second arg
@given(_strategy_bool(), _strategy_bool()) #FIXME change second arg to a custom generator for Bool
def test_Implies_bool_check(p: bool, q: bool):
  assert Implies_checkImplementation(Implies)(p, q)

#FIXME collection
#FIXME second arg
# def test_Implies1_bool_check(ps: Collection[Bool], q: Bool):
#   assert Implies1_checkImplementation(Implies1)(ps, q)

#FIXME second arg
@given(_strategy_bool(), _strategy_bool()) #FIXME change second arg to a custom generator for Bool
def test_Iff_bool_check(p: bool, q: bool):
  assert Iff_checkImplementation(Iff)(p, q)

#FIXME collection
# def test_Iff1_bool_check(bs: Collection[Bool]):
#   assert Iff1_checkImplementation(Iff1)(bs)



# VERIFY SYMBOLIC IMPLEMENTATION AGAINST REFERENCE IMPLEMENTATION

@given(_strategy_BoolRef())
def test_Not_BoolRef_check(b: z3.BoolRef):
  assert Not_checkImplementation(Not)(b)

# def test_Not1_BoolRef_check(bs: Collection[bool]):
#   assert Not1_checkImplementation(Not1)(bools_to_BoolRef1(bs), postProcess = bool_to_BoolRef1)

@given(_strategy_BoolRef(), _strategy_BoolRef())
def test_And_BoolRef_check(p: z3.BoolRef, q: z3.BoolRef):
  assert And_checkImplementation(And)(p, q)
  # assert And_checkImplementation(And)(bool_to_BoolRef1(p), bool_to_BoolRef1(q), postProcess = bool_to_BoolRef1)

# def test_And1_BoolRef_checks(bs: Collection[z3.BoolRef]):

@given(_strategy_BoolRef(), _strategy_BoolRef())
def test_Or_BoolRef_check(p: z3.BoolRef, q: z3.BoolRef):
  assert Or_checkImplementation(Or)(p, q)
  # assert Or_checkImplementation(Or)(bool_to_BoolRef1(p), bool_to_BoolRef1(q), postProcess = bool_to_BoolRef1)

# def test_Or1_BoolRef_checks(bs: Collection[z3.BoolRef]):

@given(_strategy_BoolRef(), _strategy_BoolRef())
def test_Implies_BoolRef_check(p: z3.BoolRef, q: z3.BoolRef):
  assert Implies_checkImplementation(Implies)(p, q)
  # assert Implies_checkImplementation(Implies)(bool_to_BoolRef1(p), bool_to_BoolRef1(q), postProcess = bool_to_BoolRef1)

# def test_Implies1_BoolRef_checks(bs: Collection[z3.BoolRef]):

@given(_strategy_BoolRef(), _strategy_BoolRef())
def test_Iff_BoolRef_check(p: z3.BoolRef, q: z3.BoolRef):
  assert Iff_checkImplementation(Iff)(p, q)
  # assert Iff_checkImplementation(Iff)(bool_to_BoolRef1(p), bool_to_BoolRef1(q), postProcess = bool_to_BoolRef1)

# def test_Iff1_BoolRef_checks(bs: Collection[z3.BoolRef]):
