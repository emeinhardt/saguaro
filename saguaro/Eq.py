'''
Module used to define a typeclass for equality that presents a
relationally-oriented interface ensuring seamless use with an SMT solver.
'''

from dataclasses import dataclass
from typing import TypeVar, Collection, Sequence
from classes import AssociatedType, Supports, typeclass

from saguaro.utilities import areSameLength
from saguaro._Boolean import Bool
from saguaro._Boolean import Not, Not1 \
                           , And, And1, Or, Or1 \
                           , Implies, Implies1 \
                           , Iff, Iff1

import z3


class Eq(AssociatedType):
  """Equality typeclass specifically for use in this project in concert with other binary relation typeclasses."""

E = TypeVar("E", bound=Supports[Eq])

@typeclass(Eq)
def eq(left: E, right: E) -> Bool:
  """left == right"""

@eq.instance(z3.BoolRef)
@eq.instance(bool)
def _eq_Bool(left: Bool, right: Bool) -> Bool:
  return left == right

@typeclass(Eq)
def eq1(values: Collection[E]) -> Bool:
  """Mutual equality"""

@eq1.instance(bool)
@eq1.instance(z3.BoolRef)
def _eq1_Bool(values: Collection[Bool]) -> Bool:
  return Iff(values)

@eq1.instance(object)
def _eq1_object(values: Collection[E]) -> Bool:
  values_seq = list(values)
  v0         = values_seq[0]
  return And1([eq(v0, v) for v in values_seq])

@typeclass(Eq)
def eq2(value: E, values: Collection[E]) -> Bool:
  """True if \forall i, values[i] == value"""

@eq2.instance(object)
def _eq2_object(value: E, values: Collection[E]) -> Bool:
  return And1([eq(value, v) for v in values])

@typeclass(Eq)
def eq3(value: E, values: Collection[E]) -> Bool:
  """True if \exists i, values[i] == value"""

@eq3.instance(object)
def _eq3_object(value: E, values: Collection[E]) -> Bool:
  return Or1([eq(value, v) for v in values])

@typeclass(Eq)
def elementOf(value: E, values: Collection[E]) -> Bool:
  """Synonym for eq3"""

@elementOf.instance(object)
def _elementOf(value: E, values: Collection[E]) -> Bool:
  return eq3(value, values)

@typeclass(Eq)
def eq4(lefts: Sequence[E], rights: Sequence[E]) -> Bool:
  """Pairwise equality: True if \forall i, lefts[i] == rights[i]"""

@eq4.instance(object)
def _eq4_object(lefts: Sequence[E], rights: Sequence[E]) -> Bool:
  assert areSameLength(lefts, rights)
  return And1([eq(l,r) for l,r in zip(lefts, rights)])

@typeclass(Eq)
def eq5(lefts: Collection[E], rights: Collection[E]) -> Bool:
  """True iff the left collection is contained in the other"""

@eq5.instance(object)
def _eq5_object(lefts: Collection[E], rights: Collection[E]) -> Bool:
  return And1([elementOf(l, rights) for l in lefts])

@typeclass(Eq)
def isContainedBy(lefts: Collection[E], rights: Collection[E]) -> Bool:
  """Synonym for eq5"""

@isContainedBy.instance(object)
def _isContainedBy_object(lefts: Collection[E], rights: Collection[E]) -> Bool:
  return eq5(lefts, rights)

@typeclass(Eq)
def neq(left: E, right: E) -> Bool:
  """left != right"""

@neq.instance(z3.BoolRef)
@neq.instance(bool)
def _neq_Bool(left: Bool, right: Bool) -> Bool:
  return left != right

@neq.instance(object)
def _neq_object(left: E, right: E) -> Bool:
  return Not(eq(left, right))

@typeclass(Eq)
def neq1(values: Collection[E]) -> Bool:
  """negation of eq1(values)"""

@neq1.instance(object)
# @neq1.instance(z3.BoolRef)
# @neq1.instance(bool)
# def _neq1_Bool(values: Collection[Bool]) -> Bool:
def _neq1_Bool(values: Collection[E]) -> Bool:
  return Not(eq1(values))

# A synonym - a simple example of a default implementation at the top level of a
# typeclass defined in terms of other operations (necessarilly including some
# defined by e.g. the end-user or a provided default).
@typeclass(Eq)
def distinct(left: E, right: E) -> Bool:
  """left != right"""

@distinct.instance(object)
def _distinct_object(left: object, right: object) -> Bool:
  return neq(left, right)

@typeclass(Eq)
def law_reflexivity_forAll(a: E) -> Bool:
  '''A binary relation R is reflexive iff \forall a, a R a'''

@law_reflexivity_forAll.instance(object)
def _law_reflexivity_forAll_object(a: object) -> Bool:
  return eq(a, a)

@typeclass(Eq)
def law_symmetry_forAll(a: E, b: E) -> Bool:
  '''A binary relation R is symmetric iff \forall a, b, a R b \iff b R a '''

@law_symmetry_forAll.instance(object)
def _law_symmetry_forAll_object(a: object, b: object) -> Bool:
  return (eq(a, b)) == (eq(b, a))

@typeclass(Eq)
def law_transitivity_forAll(a: E, b: E, c: E) -> Bool:
  '''A binary relation R is transitive iff \forall a, b, c, a R b \land b R c \implies a R c'''

@law_transitivity_forAll.instance(object)
def _law_transitivity_forAll_object(a: object, b: object, c: object) -> Bool:
  return Implies( And( eq(a, b)
                     , eq(b, c)
                     )
                , eq(a, c)
                )
