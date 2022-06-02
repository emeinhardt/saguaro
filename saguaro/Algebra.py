'''
Module for typeclasses representing algebraic structures like magmas,
semigroups, monoids, and so on (but not including significant order-theoretic material).
'''

from dataclasses import dataclass
from typing import TypeVar, Union, Callable, Optional
from typing import FrozenSet, Set, Tuple, List
from typing import Collection#, Sequence
from classes import AssociatedType, Supports, typeclass

import itertools

from funcy import lmap

import hypothesis
from hypothesis import strategies as st

import z3

import saguaro.utilities as SU
import saguaro.Eq        as SE
import saguaro._Boolean  as SB


from saguaro.utilities import A, B
from saguaro._Boolean import Bool \
                           , Not, Not1 \
                           , And, And1 \
                           , Or, Or1 \
                           , Implies, Implies1 \
                           , Iff, Iff1
from saguaro.Eq import Eq, eq, neq, distinct, eq1


# NB all structures here are assumed to be finite.


def is_preserved_under_over(predicate: Callable[[A], Bool], f: Callable[[A], A], universe: Collection[A]) -> Bool:
  """
  Return a proposition
     - a z3.BoolRef constraint (for Bool = z3.BoolRef)
     - a Python boolean (for Bool = bool)
  reflecting whether
    `predicate` is preserved under `f` over (each element of) `universe`
  i.e whether the collection resulting from `f` to every element of `universe`
  preserves the truth value of `predicate` over `universe`.
  """
  return And1( lmap(lambda x: Implies( predicate(  x )
                                , predicate(f(x))
                                )
                   , universe)
             )



class HasProduct:
 """
 Associated type for a typeclass representing a monoid-like structure that has
 a multiplication-like operation.

 Note that this typeclass is principally *syntactic* in nature, and is motivated
 by structures with more than one operation. For example, we can say that a
 semiring must (among other requirements) implement HasProduct and HasSum, and
 then #FIXME
 """

# @typeclass(HasProduct)
# def product(left: Mg, right: Mg) -> Mg:
#   """*"""

@typeclass(HasProduct)
def is_product(a: A, left: A, right: A) -> Bool:
  """*"""

class HasSum:
 """
 Associated type for a typeclass representing a (usually commutative) monoid-
 like structure that has an addition-like operation.
 """

# @typeclass(HasSum)
# def sum(left: Mg, right: Mg) -> Mg:
#   """+"""

@typeclass(HasSum)
def is_sum(a: A, left: A, right: A) -> Bool:
  """+"""



class Magma(Eq, HasProduct):
  """Associated type for a typeclass representing a magma type"""

Mg = TypeVar("Mg", bound=Supports[Magma])

@typeclass(Magma)
def _enumerate_Magma(mg: Mg) -> Set[Mg]: ...

# @typeclass(Magma)
# def product(left: Mg, right: Mg) -> Mg:
#   """*"""

# @typeclass(Magma)
# def is_product(value: Mg, left: Mg, right: Mg) -> Bool:
#   """*"""

@typeclass(Magma)
def commute(left: Mg, right: Mg) -> Bool: ...

@commute.instance(object)
def _commute_object(left: Mg, right: Mg) -> Bool:
 mgs = _enumerate_Magma(left) # TODO replace...
 return And1([ Iff( is_product(m, left, right)
                  , is_product(m, right, left)
                  )
               for m in mgs
             ])

@typeclass(Magma)
def law_totalAndClosed_forAll(left: Mg, right: Mg, mgs: Set[Mg]) -> Bool: ...

@law_totalAndClosed_forAll.instance(object)
def _law_totalAndClosed_forAll_object(left: Mg, right: Mg, mgs: Set[Mg]) -> Bool:
  return Or1([ is_product(value, left, right)
               for value in mgs
             ])


class Associative(Magma): ...

AS = TypeVar("AS", bound=Supports[Associative])

@typeclass(Associative)
def law_associative_forAll(a: AS, b: AS, c: AS, ASs: Optional[Set[AS]]) -> Bool: ...

@law_associative_forAll.instance(object)
def _law_associative_forAll_object(a: AS, b: AS, c: AS, ASs: Optional[Set[AS]]) -> Bool:
  # ensureEnumeration(sgs) #TODO generalize for use here
  return And1([ Implies( And1([ is_product(bpc   , b  , c)
                              , is_product(ap_bpc, a  , bpc)
                              , is_product(apb   , a  , b)
                              , is_product(apb_pc, apb, c)
                              ])
                       , eq( ap_bpc
                           , apb_pc
                           )
                       )
                 for bpc, apb, ap_bpc, apb_pc in list(itertools.product(ASs, repeat=5))  # type: ignore
               ])


class Commutative(Magma):
 """Associated type for a typeclass representing a commutative magma type"""

Co = TypeVar("Co", bound=Supports[Commutative])

@typeclass(Commutative)
def law_commute_forAll(left: Co, right: Co, cos: Set[Co]) -> Bool: ...

#FIXME default implementation


class Idempotent(Magma): ...

Ip = TypeVar("Ip", bound=Supports[Idempotent])

@typeclass(Idempotent)
def law_idempotent_forAll(i: Ip, ips: Optional[Set[Ip]]) -> Bool: ...


class HasIdentity(Magma): ...

Id = TypeVar("Id", bound=Supports[HasIdentity])

@typeclass(HasIdentity)
def is_identity(i: Id, ids: Optional[Set[Id]]) -> Bool: ...

#FIXME default implementation

@typeclass(HasIdentity)
def law_twoSidedIdentity_forAll(a: Id, ids: Optional[Set[Id]]): ...

@typeclass(HasIdentity)
def law_uniqueIdentityExists_forAll(a: Id) -> Bool: ...


class HasInverses(HasIdentity): ...

Iv = TypeVar("Iv", bound=Supports[HasInverses])

# @typeclass(HasInverses)
# def inverses(a: Iv, b: Iv, ivs: Optional[Set[Iv]]): ...



class Semigroup(Associative):
  """Associated type for a typeclass representing a semigroup type"""

Sg = TypeVar("Sg", bound=Supports[Semigroup])



class Band(Semigroup, Idempotent): ...

class LeftRegularBand(Band): ...

LRB = TypeVar("LRB", bound=Supports[LeftRegularBand])

@typeclass(LeftRegularBand)
def law_leftRegularBand_forAll(a: LRB, b: LRB, lrbs: Optional[Set[LRB]]) -> Bool: ...



class Monoid(Semigroup, HasIdentity):
  """Associated type for a typeclass representing a monoid type"""

Mn = TypeVar("Mn", bound=Supports[Monoid])

#FIXME default implementation

#FIXME default implementation



class Group(Monoid):
  """Associated type for a typeclass representing a group type"""

G = TypeVar("G", bound=Supports[Group])

@typeclass(Group)
def law_uniqueInverseExists_Group_forAll(a: G, gs: Set[G]): ...

#FIXME default implementation



# class Semiring(HasProduct, HasSum): ...

# SR = TypeVar("SR", bound=Supports[Semiring])

# @typeclass(Semiring)
# def multiplicative_identity(sr: SR) -> SR: ...

# @typeclass(Semiring)
# def additive_identity(sr: SR) -> SR: ...

# # law_totalAndClosed_forAll
# @typeclass(Semiring)
# def law_product_is_magma() -> Bool:

# # law_associative_forAll
# def law_product_is_semigroup() -> Bool:

# # law_uniqueIdentityExists_forAll
# @typeclass(Semiring)
# def law_product_is_monoid() -> Bool:

# # law_totalAndClosed_forAll
# @typeclass(Semiring)
# def law_sum_is_magma() -> Bool:

# # law_associative_forAll
# def law_sum_is_semigroup() -> Bool:

# # law_uniqueIdentityExists_forAll
# @typeclass(Semiring)
# def law_sum_is_monoid() -> Bool:

# # law_
# @typeclass(Semiring)
# def law_sum_is_commutative() -> Bool:

# @typeclass(Semiring)
# def law_additiveIdentity_is_multiplicativeAnnihilator() -> Bool:

# @typeclass(Semiring)
# def law_product_left_distributes_over_sum() -> Bool:

# @typeclass(Semiring)
# def law_product_right_distributes_over_sum() -> Bool:

# # @typeclass(Semiring)
# # def law_hasAdditiveIdentity_forAll(sr: SR) -> Bool: ...


# *Left* near-ring
class Nearring(HasProduct, HasSum): ...

NR = TypeVar("NR", bound=Supports[Nearring])

@typeclass(Nearring)
def multiplicative_identity(nr: NR) -> NR: ...

@typeclass(Nearring)
def additive_identity(nr: NR) -> NR: ...

# law_totalAndClosed_forAll
@typeclass(Nearring)
def law_product_is_magma() -> Bool: ...

# law_associative_forAll
def law_product_is_semigroup() -> Bool: ...

# law_uniqueIdentityExists_forAll
@typeclass(Nearring)
def law_product_is_monoid() -> Bool: ...

# law_totalAndClosed_forAll
@typeclass(Nearring)
def law_sum_is_magma() -> Bool: ...

# law_associative_forAll
def law_sum_is_semigroup() -> Bool: ...

# law_uniqueIdentityExists_forAll
@typeclass(Nearring)
def law_sum_is_monoid() -> Bool: ...

# NB the group is *not* necessarily commutative!
# law_
@typeclass(Nearring)
def law_sum_is_group() -> Bool: ...

@typeclass(Nearring)
def law_additiveIdentity_is_multiplicativeAnnihilator() -> Bool: ...

@typeclass(Nearring)
def law_product_left_distributes_over_sum() -> Bool: ...

# @typeclass(Nearring)
# def law_hasAdditiveIdentity_forAll(nr: NR) -> Bool: ...

