# from collections.abc import Collection, Mapping, Sequence
# import collections.abc as cabc
# import typing
# from collections.abc import Collection, Sequence#, Mapping
# from typing import get_args#, overload, TypeVar
# from typing import Optional, Union#, Collection, Sequence
# from typing import Collection, Sequence, Tuple, List, Set, FrozenSet
# from classes import AssociatedType, Supports, typeclass

# from funcy import lmap
# from functools import reduce

import hypothesis
from hypothesis import given, strategies as st
# import pytest

import z3

# import saguaro.utilities as SU
# from saguaro.utilities import foldl, A
# import saguaro._Boolean as SB
from saguaro._Boolean import _strategy_bool, _strategy_BoolRef
from saguaro._Boolean import Not, Not1, And, And1, Or, Or1, Implies, Implies1, Iff, Iff1
from saguaro._Boolean import Bool
# import saguaro.Eq as Eq
from saguaro.Eq import eq, eq1, \
  neq, distinct, \
  law_reflexivity_forAll, \
  law_symmetry_forAll, \
  law_transitivity_forAll

def test_should_pass():
  assert False == False

# def test_should_fail():
#   assert False == True


# Goal of "basic" tests is simply to check that every call of
# every type signature expected is defined and has the expected type


@given(_strategy_bool, _strategy_bool)
def Eq_implementations_type_basic(p: bool, q: bool):
  assert type( eq(p,     p ))        == bool
  assert type(neq(p, Not(p)))        == bool
  assert type(    eq1([p,     p ]) ) == bool
  assert type(Not(eq1([p, Not(p)]))) == bool
  #eq2-5 ...

  assert type(  eq(z3.BoolVal(p),     z3.BoolVal(p) ) )        == z3.BoolRef
  assert type( neq(z3.BoolVal(p), Not(z3.BoolVal(p))) )        == z3.BoolRef
  assert type(     eq1([z3.BoolVal(p),     z3.BoolVal(p) ])  ) == z3.BoolRef
  assert type( Not(eq1([z3.BoolVal(p), Not(z3.BoolVal(p))])) ) == z3.BoolRef
  #eq2-5 ...

@given(_strategy_bool, _strategy_bool)
def Eq_implementations_value_basic(p: bool, q: bool):

  assert  eq(p,     p )
  assert neq(p, Not(p))
  assert     eq1([p,     p ])
  assert Not(eq1([p, Not(p)]))
  # assert     eq2([p,     p ], p)
  # assert Not(eq2([p, Not(p)], p))
  # assert     eq3([    p , Not(p)], p)
  # assert Not(eq3([Not(p), Not(p)], p))
  # assert     eq4([    p , Not(p)], [    p , Not(p)])
  # assert Not(eq4([Not(p), Not(p)], [    p , Not(p)]))
  # assert     eq5({    p , Not(p)}, {    p , Not(p)})
  # assert Not(eq5({Not(p), Not(p)}, {    p , Not(p)}))

  assert  eq(z3.BoolVal(p),     z3.BoolVal(p) )
  assert neq(z3.BoolVal(p), Not(z3.BoolVal(p)))
  assert     eq1([z3.BoolVal(p),     z3.BoolVal(p) ] )
  assert Not(eq1([z3.BoolVal(p), Not(z3.BoolVal(p))]))
  #eq2-5 ...

@given(_strategy_bool)
def Eq_law_reflexivity_bool(b: bool):
  assert law_reflexivity_forAll(b)

@given(_strategy_bool, _strategy_bool)
def Eq_law_symmetry_bool(p: bool, q: bool):
  assert law_symmetry_forAll(p, q)

@given(_strategy_bool, _strategy_bool, _strategy_bool)
def Eq_law_transitivity_bool(p: bool, q: bool, r: bool):
  assert law_transitivity_forAll(p, q, r)

@given(_strategy_BoolRef)
def Eq_law_reflexivity_BoolRef(b: z3.BoolRef):
  assert law_reflexivity_forAll(b)

@given(_strategy_BoolRef, _strategy_BoolRef)
def Eq_law_symmetry_BoolRef(p: z3.BoolRef, q: z3.BoolRef):
  assert law_symmetry_forAll(p, q)

@given(_strategy_BoolRef, _strategy_BoolRef, _strategy_BoolRef)
def Eq_law_transitivity_BoolRef(p: z3.BoolRef, q: z3.BoolRef, r: z3.BoolRef):
  assert law_transitivity_forAll(p, q, r)

