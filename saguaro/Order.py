'''
Module for typeclasses representing partial orders and related elaborations.

To understand 60% of the contents of this file, you need to be comfortable with
looking up elementary types of order-theoretic structures and results about them
  - Wikipedia is decent; an undergraduate-level introductory text on order-theory
    or Boolean algebra will cover almost everything.
    - #FIXME add annotated bibliography to docs


Note that it is assumed that all structures are finite; this assumption
manifests in at least two ways:
  - Some key functions (or specifically laws) have a straightforward default
    implementation when you can iterate over the whole enumerated structure
    (preorder, powerset, etc.).
      - This is obviously not scalable, but it is useful for testing and
        provides an invaluable executable, interactive type of documenation that
        communicates the meaning of more sophisticated implementations or more
        complex instances.
  - The hierarchy of typeclasses contains gaps or seeming jumps explainable in
  light of the finiteness assumption. For example, every finite lattice is a
  complete lattice and hence complete lattices are not mentioned anywhere here,
  even though there are functions (or typeclasses demanding certain functions)
  that in some way reflect the assumption that every lattice under consideration
  is complete.
'''

from dataclasses import dataclass
from typing import TypeVar, Generic, Union, Optional#, Callable,
from typing import FrozenSet, Set, Tuple, List#, Sequence
from classes import AssociatedType, Supports, typeclass

from itertools import product

import hypothesis
from hypothesis import strategies as st

import z3

from saguaro.utilities import A, peek, isNonempty, ensureNonnull
from saguaro.Algebra import is_preserved_under_over, Monoid
from saguaro._Boolean import Bool, Constraint \
                           , Not, Not1 \
                           , And, And1 \
                           , Or, Or1 \
                           , Implies, Implies1 \
                           , Iff, Iff1
from saguaro.Eq import Eq, eq, neq, distinct, eq1



# NB all structures here are assumed to be finite.

class Preorder(Eq): ...

P = TypeVar("P", bound=Supports[Preorder])

class _Set_Preorder_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, Set) \
             and (   len(arg) == 0 \
               or isinstance(peek(arg), Preorder)
               )
    except Exception:
      return False

class Set_Preorder(Set[Preorder], metaclass=_Set_Preorder_Meta): ...

class _FrozenSet_Preorder_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, FrozenSet) \
             and (   len(arg) == 0 \
               or isinstance(peek(arg), Preorder)
               )
    except Exception:
      return False

class FrozenSet_Preorder(FrozenSet[Preorder], metaclass=_FrozenSet_Preorder_Meta): ...

# TODO - This type/associated typeclass method is currently unused.
#  - short term: comment it + instance definitions out
#  - long term: when you've gotten to the expected use case (reasoning about _ and
#  sub_s), decide if there's a compelling reason to keep this around.
@dataclass(frozen=True)
class _Enumeration(Generic[P]):
  values: FrozenSet[P]

  def unwrap(self) -> FrozenSet[P]:
    return self.values

  def thaw(self) -> Set[P]:
    return set(self.values)

  def linearize(self) -> Tuple[P, ...]:
    return tuple(sorted(self.values))

  @staticmethod
  def freeze(s: Set[P]) -> '_Enumeration[P]':
    return _Enumeration(values = frozenset(s))

@dataclass(frozen=True)
class _ConcreteEnumeration(_Enumeration[P]):

  @staticmethod
  def freeze(s: Set[P]) -> '_ConcreteEnumeration[P]':
    return _ConcreteEnumeration(values = frozenset(s))

@dataclass(frozen=True)
class _SymbolicEnumeration(_Enumeration[P]):
  constraint: Constraint

  @staticmethod
  def freeze(s: Set[P], c: Constraint) -> '_SymbolicEnumeration[P]':  # type: ignore
    return _SymbolicEnumeration(values = frozenset(s), constraint = c)

def ensureEnumeration(ps: Optional[Set[P]]) -> bool:
  return ensureNonnull(ps, f"The default implementation requires a non-null enumeration `ps`.")

@typeclass(Preorder)
def _enumerate_Preorder(p: P) -> _Enumeration[P]:
  '''
  Generate the entire free preorder containing p

  This method exists
    (1) to allow some useful default implementations elsewhere in this file to exist
    (2) because all applications of this library involve finite structures
    (3) as a typeclass method to insulate the aforementioned default implementations
        from imposing or relying on any particular way of allowing the free preorder
        associated with an element to be generated from that element
  '''

# @typeclass(Preorder)
# def _enumerate_Preorder(atoms: Set[P]) -> Set[P]:
#   '''
#   Generates an entire finite preorder from `atoms`.
#   '''

# @typeclass(Preorder)
# def is_cartesian_product(product: Set[Tuple[P, P]], left: Set[P], right: Set[P]) -> Bool: ...
# # FIXME wait til there's a need for it to explore how much work it is in Python
# # these days to make an ergonomic interface that expresses the idea
# # "a product of preorders induces a preorder..."...

# @typeclass(Preorder)
# def is_linear_sum(linear_sum: Set[P], left: Set[P], right: Set[P]) -> Bool:
#   '''
#   `s` is the linear sum of `l` and `r` iff
#     `s` can be formed by 'connecting' each of the maximal elements of `l` with every minimal element of `r`
#   '''

# @typeclass(Preorder)
# def is_disjoint_union(disjoint_union: Set[P], left: Set[P], right: Set[P]) -> Bool:
#   '''
#   `u` is the disjoint union of `l` and `r` iff
#     `x` \leq_u y iff (x,y \in l \and x \leq_l y) \lor (x,y \in r \and x \leq_r y)
#   '''

@typeclass(Preorder)
def le(left: P, right: P) -> Bool:
  """<="""

@typeclass(Preorder)
def ge(left: P, right: P) -> Bool:
  """>="""

@typeclass(Preorder)
def comparable(left: P, right: P) -> Bool:
  """<= | >="""

@comparable.instance(object)
def _comparable_object(left: P, right: P) -> Bool:
  return Or( le(left , right)
           , le(right, left )
           )

@typeclass(Preorder)
def lt(left: P, right: P) -> Bool:
  """<"""

@lt.instance(object)
def _lt_object(left: P, right: P) -> Bool:
  return And(     le(left , right)
            , Not(le(right, left ))
            )

@typeclass(Preorder)
def gt(left: P, right: P) -> Bool:
  """>"""

@gt.instance(object)
def _gt_object(left: P, right: P) -> Bool:
  return And(     ge(left , right)
            , Not(ge(right, left ))
            )

@typeclass(Preorder)
def is_between(p: P, l: P, u: P) -> Bool:
  '''p is between l and u iff l \leq p \leq u'''

@is_between.instance(object)
def _is_between_object(p: P, l: P, u: P) -> Bool:
  return is_in_interval(p, l, u)

# @typeclass(Preorder)
# def is_interval(s: Set[P], l: P, u: P, ps: Set[p]) -> Bool:
#   '''p is in [l, u] iff l \leq p \leq u'''

# @is_interval.instance(object)
# def _is_interval_object(s: Set[P], l: P, u: P, ps: Set[p]) -> Bool:
#   return And1([ elementOf(l, ps)
#               , elementOf(u, ps)
#               ] +
#               [ elementOf(p, ps) for p in s ] +
#               [ Iff(is_between(p, l, u), elementOf(p, s)) for p in ps ]
#               )

@typeclass(Preorder)
def is_in_interval(p: P, l: P, u: P) -> Bool:
  '''p is in [l, u] iff l \leq p \leq u'''

@is_in_interval.instance(object)
def _is_in_interval_object(p: P, l: P, u: P) -> Bool:
  return And( le(l, p), le(p, u) )

# @typeclass(Preorder)
# def is_lower_closure(s: Set[P], a: P, ps: Set[P]) -> Bool:
#   '''The lower closure of a with respect to a partially ordered set ps = {p \in ps | p \leq a}'''

# @is_lower_closure.instance(object)
# def _is_lower_closure_object(s: Set[P], a: P, ps: Set[P]) -> Bool:
#   return And1([ elementOf(a, ps)
#               , elementOf(a, s )
#               ] +
#               [ elementOf(p, ps) for p in s ] +
#               [ Iff(le(p, a), elementOf(p, s)) for p in ps]
#               )

# @typeclass(Preorder)
# def is_in_lower_closure(p: P, a: P, ps: Set[P]) -> Bool:
#   '''The lower closure of a with respect to a partially ordered set ps = {p \in ps | p \leq a}'''

# @is_in_lower_closure.instance(object)
# def _is_in_lower_closure_object(p: P, a: P, ps: Set[P]):
#   return And1([ elementOf(p, ps)
#               , elementOf(a, ps)
#               , le(p, a)
#               ])
#   # return filter(lambda b: le(b, a), ps)

# @typeclass(Preorder)
# def is_upper_closure(s: Set[P], a: P, ps: Set[P]) -> Bool:
#   '''The upper closure of a with respect to a partially ordered set ps = {p \in ps | a \leq p}'''

# @is_upper_closure.instance(object)
# def _is_upper_closure_object(s: Set[P], a: P, ps: Set[P]) -> Bool:
#   return And1([ elementOf(a, ps)
#               , elementOf(a, s)
#               ] +
#               [ elementOf(p, ps) for p in s ] +
#               [ Iff(le(a, p), elementOf(p, s)) for p in ps]
#               )

# @typeclass(Preorder)
# def is_in_upper_closure(p: P, a: P, ps: Set[P]) -> Bool:
#   '''The upper closure of a with respect to a partially ordered set ps = {p \in ps | p \leq a}'''

# @is_in_upper_closure.instance(object)
# def _is_in_upper_closure_object(p: P, a: P, ps: Set[P]):
#   return And1([ elementOf(p, ps)
#               , elementOf(a, ps)
#               , le(a, p)
#               ])
#   # return filter(lambda b: le(a, b), ps)

@typeclass(Preorder)
def is_maximal(a: P, ps: Set[P]) -> Bool:
  '''a is a maximal element of ps iff \forall p, a \leq p \implies p \leq a'''

@is_maximal.instance(object)
def _is_maximal_object(a: P, ps: Set[P]) -> Bool:
  return And1([ Implies( le(a, p)
                       , le(p, a)  # synonymous with p == a ('is identical to') for partial orders (but not for preorders/directed sets)
                       )
                for p in ps
              ])

@typeclass(Preorder)
def is_minimal(a: P, ps: Set[P]) -> Bool:
  '''a is a minimal element of ps iff \forall p, p \leq a \implies a \leq p'''

@is_minimal.instance(object)
def _is_minimal_object(a: P, ps: Set[P]) -> Bool:
  return And1([ Implies( le(p, a)
                       , le(a, p)  # synonymous with p == a ('is identical to') for partial orders (but not for preorders/directed sets)
                       )
                for p in ps
              ])

@typeclass(Preorder)
def is_least(a: P, ps: Set[P]) -> Bool:
  '''
  a is a least element among ps iff \forall p, a \leq p

  NB that a least element is necessarily unique when ps is a partial order.
  '''

@is_least.instance(object)
def _is_least_object(a: P, ps: Set[P]) -> Bool:
  return And1([ le(a, p)
                for p in ps
              ])

@typeclass(Preorder)
def is_greatest(a: P, ps: Set[P]) -> Bool:
  '''
  a is a greatest element among ps iff \forall p, p \leq a

  NB that a greatest element is necessarily unique when ps is a partial order.
  '''

@is_greatest.instance(object)
def _is_greatest_object(a: P, ps: Set[P]) -> Bool:
  return And1([ le(p, a)
                for p in ps
              ])

@typeclass(Preorder)
def is_upper_bound(a: P, ps: Set[P]) -> Bool:
  '''a is an upper bound of ps iff \forall p, p \leq a'''

@is_upper_bound.instance(object)
def _is_upper_bound_object(a: P, ps: Set[P]) -> Bool:
  return And1([le(p, a) for p in ps])

# @typeclass(Preoder)
# def has_upper_bound(ps: Set[P]) -> Bool: ...

# @has_upper_bound.instance(object)
# def _has_upper_bound_object(ps: Set[P]) -> Bool:
#   return Or1([
#                for p in ps
#              ])

@typeclass(Preorder)
def gt1(a: P, ps: Set[P]) -> Bool: ...

@gt1.instance(object)
def _gt1_object(a: P, ps: Set[P]) -> Bool:
  return is_upper_bound(a, ps)

@typeclass(Preorder)
def is_lower_bound(a: P, ps: Set[P]) -> Bool:
  '''a is a lower bound of ps iff \forall p, a \leq p'''

@is_lower_bound.instance(object)
def _is_lower_bound_object(a: P, ps: Set[P]) -> Bool:
  return And1([le(a, p) for p in ps])

@typeclass(Preorder)
def lt1(a: P, ps: Set[P]) -> Bool: ...

@lt1.instance(object)
def _lt1_object(a: P, ps: Set[P]) -> Bool:
  return is_lower_bound(a, ps)

@typeclass(Preorder)
def is_least_upper_bound(a: P, left: P, right: P, ps: Optional[Set[P]]) -> Bool:
  '''
  Let `a`, `l`, `r` \in some preorder `p`.
  `a` is the least upper bound of `{l, r}` (where `{l, r}` \subseteq `p`) iff `a`
  is minimal among the upper bounds of `{l, r}` in `p`

  If `ps` is provided, it is considered to be an enumeration of the preorder `p`.
  The default implementation requires this to be provided.

  Even when `ps` is not *necessary*, if it is provided, the effect will be to
  calculate whether (or assert that) `a` is the least upper bound of `{l, r}`
  wrt the preorder defined by (just) *ps*.
  '''

@is_least_upper_bound.instance(object)
def _is_least_upper_bound_object(a: P, left: P, right: P, ps: Optional[Set[P]]) -> Bool:
  '''
  a is the least upper bound of (left, right) wrt the preorder formed by `ps` iff
   - a is an upper bound of (left, right)
   - \forall b in Ps,
      if b is an upper bound of (left, right), then b \leq a implies a \leq b
  '''
  ensureEnumeration(ps)
  return And( And( le(left , a)
                 , le(right, a)
                 )
            , And1([ Implies( And( le(left , b)
                                 , le(right, b)
                                 )
                            , Implies( le(b, a)
                                     , le(a, b)
                                     )
                            )
                     for b in ps  # type: ignore
                   ])
            )

@typeclass(Preorder)
def is_least_upper_bound1(a: P, s: Set[P], ps: Optional[Set[P]]) -> Bool:
  '''
  Let `a` be an element of some preorder `p` and let `s` be a subset of `p`.
  `a` is the least upper bound of `s` iff `a` is minimal among the upper bounds
  of `s` in `ps`

  If `ps` is provided, it is considered to be an enumeration of the preorder
  `p`. The default implementation requires this to be provided.

  Even when `ps` is not *necessary*, if it is provided, the effect will be to
  calculate whether (or assert that) `a` is the least upper bound of `s` wrt
  the preorder defined by (just) *ps*.
  '''

@is_least_upper_bound1.instance(object)
def _is_least_upper_bound1_object(a: P, s: Set[P], ps: Optional[Set[P]]) -> Bool:
  ensureEnumeration(ps)
  return And( And1([ le(p, a)
                     for p in s
                   ])
            , And1([ Implies( And1([ le(p, b)
                                     for p in s
                                   ])
                            , Implies( le(b, a)
                                     , le(a, b)
                                     )
                            )
                     for b in ps  # type: ignore
                   ])
                 )

@typeclass(Preorder)
def is_join(a: P, left: P, right: P, ps: Optional[Set[P]]) -> Bool: ...

@is_join.instance(object)
def _is_join_object(a: P, left: P, right: P, ps: Optional[Set[P]]) -> Bool:
  return is_least_upper_bound(a, left, right, ps)

@typeclass(Preorder)
def is_join1(a: P, s: Set[P], ps: Optional[Set[P]]) -> Bool: ...

@is_join1.instance(object)
def _is_join1_object(a: P, s: Set[P], ps: Optional[Set[P]]) -> Bool:
  return is_least_upper_bound1(a, s, ps)

@typeclass(Preorder)
def has_least_upper_bound(left: P, right: P, ps: Optional[Set[P]]) -> Bool: ...

@has_least_upper_bound.instance(object)
def _has_least_upper_bound_object(left: P, right: P, ps: Optional[Set[P]]) -> Bool:
  ensureEnumeration(ps)
  return Or1([ is_least_upper_bound(a, left, right, ps)
               for a in ps  # type: ignore
             ])

@typeclass(Preorder)
def has_join(left: P, right: P, ps: Optional[Set[P]]) -> Bool: ...

@has_join.instance(object)
def _has_join_object(left: P, right: P, ps: Optional[Set[P]]) -> Bool:
  return has_least_upper_bound(left, right, ps)

@typeclass(Preorder)
def has_least_upper_bound1(s: Set[P], ps: Optional[Set[P]]) -> Bool: ...

@has_least_upper_bound1.instance(delegate=Set_Preorder)
def _has_least_upper_bound1_object(s: Set[P], ps: Optional[Set[P]]) -> Bool:
  ensureEnumeration(ps)
  assert isNonempty(s)
  return Or1([ is_least_upper_bound1(a, s, ps)
               for a in ps  # type: ignore
             ])

@typeclass(Preorder)
def has_join1(s: Set[P], ps: Optional[Set[P]]) -> Bool: ...

@has_join1.instance(delegate=Set_Preorder)
def _has_join1_object(s: Set[P], ps: Optional[Set[P]]) -> Bool:
  return has_least_upper_bound1(s, ps)

@typeclass(Preorder)
def is_greatest_lower_bound(a: P, left: P, right: P, ps: Optional[Set[P]]) -> Bool:
  '''
  Let `a`, `l`, `r` \in some preorder `p`.
  `a` is the greatest lower bound of `l` and `r` iff `a` is maximal among the lower bounds of `{l,r}`

  If `ps` is provided, it is considered to be an enumeration of the preorder `p`. The default implementation requires this to be provided.
  '''

@is_greatest_lower_bound.instance(object)
def _is_greatest_lower_bound_object(a: P, left: P, right: P, ps: Optional[Set[P]]) -> Bool:
  '''
  a is the greatest lower bound of (left, right) wrt the preorder formed by `ps` iff
   - a is a lower bound of (left, right)
  \forall b in Ps,
    if b is a lower bound of (left, right), then a \leq b implies b \leq a
  '''
  ensureEnumeration(ps)
  return And( And( le(a , left)
                 , le(a, right)
                 )
            , And1([ Implies( And( le(b, left)
                                 , le(b, right)
                                 )
                            , Implies( le(a, b)
                                     , le(b, a)
                                     )
                            )
                     for b in ps  # type: ignore
                   ])
            )

@typeclass(Preorder)
def is_greatest_lower_bound1(a: P, s: Set[P], ps: Optional[Set[P]]) -> Bool:
  '''
  Let `a` \in some preorder `p`, let `s` \subseteq `p`.
  `a` is the greatest lower bound of `s` iff `a` is maximal among the lower
  bounds of `{l,r}` in `ps`

  If `ps` is provided, it is considered to be an enumeration of the preorder
  `p`. The default implementation requires this to be provided.
  '''

@is_greatest_lower_bound1.instance(object)
def _is_greatest_lower_bound1_object(a: P, s: Set[P], ps: Optional[Set[P]]) -> Bool:
  ensureEnumeration(ps)
  return And( And1([ le(a, p)
                     for p in s
                   ])
            , And1([ Implies( And1([ le(b, p)
                                     for p in s
                                   ])
                            , Implies( le(a, b)
                                     , le(b, a)
                                     )
                            )
                     for b in ps  # type: ignore
                   ])
            )

@typeclass(Preorder)
def is_meet(a: P, left: P, right: P, ps: Optional[Set[P]]) -> Bool: ...

@is_meet.instance(object)
def _is_meet_object(a: P, left: P, right: P, ps: Optional[Set[P]]) -> Bool:
  return is_greatest_lower_bound(a, left, right, ps)

@typeclass(Preorder)
def is_meet1(a: P, s: Set[P], ps: Optional[Set[P]]) -> Bool: ...

@is_meet1.instance(object)
def _is_meet1_object(a: P, s: Set[P], ps: Optional[Set[P]]) -> Bool:
  return is_greatest_lower_bound1(a, s, ps)

@typeclass(Preorder)
def has_greatest_lower_bound(left: P, right: P, ps: Optional[Set[P]]) -> Bool: ...

@has_greatest_lower_bound.instance(object)
def _has_greatest_lower_bound_object(left: P, right: P, ps: Optional[Set[P]]) -> Bool:
  ensureEnumeration(ps)
  return Or1([ is_greatest_lower_bound(a, left, right, ps)
               for a in ps  # type: ignore
             ])

@typeclass(Preorder)
def has_meet(left: P, right: P, ps: Optional[Set[P]]) -> Bool: ...

@has_meet.instance(object)
def _has_meet_object(left: P, right: P, ps: Optional[Set[P]]) -> Bool:
  return has_greatest_lower_bound(left, right, ps)

@typeclass(Preorder)
def has_greatest_lower_bound1(s: Set[P], ps: Optional[Set[P]]) -> Bool: ...

@has_greatest_lower_bound1.instance(delegate=Set_Preorder)
def _has_greatest_lower_bound1_object(s: Set[P], ps: Optional[Set[P]]) -> Bool:
  ensureEnumeration(ps)
  assert isNonempty(s)
  return Or1([ is_greatest_lower_bound1(a, s, ps)
               for a in ps  # type: ignore
             ])

@typeclass(Preorder)
def has_meet1(s: Set[P], ps: Optional[Set[P]]) -> Bool: ...

@has_meet1.instance(delegate=Set_Preorder)
def _has_meet1_object(s: Set[P], ps: Optional[Set[P]]) -> Bool:
  return has_greatest_lower_bound1(s, ps)

@typeclass(Preorder)
def covers(c: P, a: P, ps: Optional[Set[P]]) -> Bool:
 '''`c` covers `a` iff there is no `b` in `Ps` (distinct from `a`, `c`) such that `a` \leq `b` \leq `c`'''

@covers.instance(object)
def _covers_object(c: P, a: P, ps: Optional[Set[P]]) -> Bool:
  ensureEnumeration(ps)
  return And1([ le(a, c)
              , distinct(a, c)
              ] + \
              [ Implies( And( distinct(b, c)
                            , distinct(b, a)
                            )
                       , Not(is_between(b, a, c))
                       )
                for b in ps  # type: ignore
              ]
              )

@typeclass(Preorder)
def is_chain(ps: Set[P]) -> Bool:
  '''A subset ps of a preorder is a chain iff there is a total order on ps'''

@is_chain.instance(delegate=Set_Preorder)
def _is_chain_object(ps: Set[P]) -> Bool:
  return And1([comparable(a,b) for a,b in product(ps, repeat=2)])

# @typeclass(Preorder)
# def is_descending_chain(ps: Set[P]) -> Bool: ...

# @typeclass(Preorder)
# def is_ascending_chain(ps: Set[P]) -> Bool: ...

# @typeclass(Preorder)
# def is_antichain(ps: Set[P]) -> Bool:
#   '''A subset ps of a preorder is an antichain iff every pair of elements is incomparable'''

# @typeclass(Preorder)
# def are_dual(ps: Set[P], qs: Set[P]) -> Bool:
#   '''Finite preorders `ps` and `qs` are dual iff
#      - they have the same elements
#      - `le(a, b)` holds in `ps` iff `le(b, a)` holds in `qs`'''

@typeclass(Preorder)
def law_reflexivity_forAll(p: P) -> Bool:
  '''A binary relation `R` is reflexive iff \forall `a`, `a R a`'''

@law_reflexivity_forAll.instance(object)
def _law_reflexivity_forAll_object(p: object) -> Bool:
  return le(p, p)

@typeclass(Preorder)
def law_transitivity_forAll(a: P, b: P, c: P) -> Bool:
  '''A binary relation `R` is transitive iff \forall `a`, `b`, `c`, `a R b` \and `b R c` \implies `a R c`'''

@law_transitivity_forAll.instance(object)
def _law_transitivity_forAll_object(a: object, b: object, c: object) -> Bool:
  return Implies( And( le(a, b)
                     , le(b, c)
                     )
                , le(a, c)
                )



class LowerBounded(Preorder):
  '''Associated type for a typeclass representing a preordered type with a least element'''

LB = TypeVar("LB", bound=Supports[LowerBounded])

class _Set_LowerBounded_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, Set) \
             and (   len(arg) == 0 \
               or isinstance(peek(arg), LowerBounded)
               )
    except Exception:
      return False

class Set_LowerBounded(Set[LowerBounded], metaclass=_Set_LowerBounded_Meta): ...

@typeclass(LowerBounded)
def global_lower_bound(p: LB, ps: Optional[Set[LB]]) -> LB: ...

@typeclass(LowerBounded)
def is_global_lower_bound(p: LB, ps: Optional[Set[LB]]) -> Bool: ...

@is_global_lower_bound.instance(object)
def _is_global_lower_bound_object(p: LB, ps: Optional[Set[LB]]) -> Bool:
  return is_greatest_lower_bound1(p, ps, ps)

@typeclass(LowerBounded)
def is_atom(a: LB, ps: Optional[Set[LB]]) -> Bool:
  '''
  Let `a` \in a lower-bounded preorder `ps` with bottom element `bot`.
  `a` is an atom iff `a` covers `bot`.
  '''

@is_atom.instance(object)
def _is_atom_object(a: LB, ps: Optional[Set[LB]]):
  ensureEnumeration(ps)
  return And1([ Implies( is_global_lower_bound(b, ps)
                       , covers(a, b, ps)
                       )
                for b in ps  # type: ignore
              ])
  # bot = global_lower_bound(a, ps)
  # return covers(a, bot, ps)

@typeclass(LowerBounded)
def is_atom1(atoms: Set[LB], ps: Optional[Set[LB]]): ...

@is_atom1.instance(delegate=Set_LowerBounded)
def _is_atom1_object(atoms: Set[LB], ps: Optional[Set[LB]]):
  return And1([ _is_atom_object(a, ps)
                for a in atoms
              ])

@typeclass(LowerBounded)
def law_lowerBounded(ps: Set[LB]) -> Bool:
  '''Given a finite preorder `ps`, `ps` is lower bounded iff at least one element is the global lower bound.'''

@law_lowerBounded.instance(delegate=Set_LowerBounded)
def _law_lowerBounded_object(ps: Set[LB]) -> Bool:
  return Or1([ is_global_lower_bound(p, ps)
               for p in ps
            ])



class UpperBounded(Preorder):
  '''Associated type for a typeclass representing a preordered type with a greatest element'''

UB = TypeVar("UB", bound=Supports[UpperBounded])

class _Set_UpperBounded_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, Set) \
             and (   len(arg) == 0 \
               or isinstance(peek(arg), UpperBounded)
               )
    except Exception:
      return False

class Set_UpperBounded(Set[UpperBounded], metaclass=_Set_UpperBounded_Meta): ...

@typeclass(UpperBounded)
def global_upper_bound(p: UB, ps: Optional[Set[P]]) -> UB: ...

@typeclass(UpperBounded)
def is_global_upper_bound(p: UB, ps: Optional[Set[UB]]) -> Bool: ...

@is_global_upper_bound.instance(object)
def _is_global_upper_bound_object(p: UB, ps: Optional[Set[UB]]) -> Bool:
  return is_least_upper_bound1(p, ps, ps)

@typeclass(UpperBounded)
def law_upperBounded(ps: Set[UB]) -> Bool:
  '''Given a finite preorder `ps`, `ps` is upper bounded iff at least one element is the global upper bound.'''

@law_upperBounded.instance(delegate=Set_UpperBounded)
def _law_upperBounded_object(ps: Set[UB]) -> Bool:
  ensureEnumeration(ps)
  return Or1([ is_global_upper_bound(p, ps)
               for p in ps
            ])



# Topology stub:
# https://en.wikipedia.org/wiki/Directed_set
# https://en.wikipedia.org/wiki/Net_(mathematics)
# https://en.wikipedia.org/wiki/Domain_theory
# https://en.wikipedia.org/wiki/Complete_partial_order
# https://en.wikipedia.org/wiki/Ultrafilter
# https://en.wikipedia.org/wiki/Filters_in_topology#Stone_topology
# https://en.wikipedia.org/wiki/Stone_space
# https://en.wikipedia.org/wiki/Filters_in_topology
# https://en.wikipedia.org/wiki/Stone%27s_representation_theorem_for_Boolean_algebras
# https://en.wikipedia.org/wiki/Discrete_space

# class UpperDirectedSet(Preorder): ...

# UDS = TypeVar("UDS", bound=Supports[UpperDirectedSet])

# @typeclass
# def law_joinable_forAll(a: UDS, b: UDS) -> Bool:
#   '''A preorder ps is an upper directed set iff \forall a, b,  upper_bound(a, b) exists and is in ps'''

# class LowerDirectedSet(Preorder): ...

# LDS = TypeVar("LDS", bound=Supports[LowerDirectedSet])

# @typeclass
# def law_meetable_forAll(a: LDS, b: LDS) -> Bool:
#   '''A preorder ps is an upper directed set iff \forall a, b,  lower_bound(a, b) exists and is in ps'''



class PartialOrder(Preorder):
  """Associated type for a typeclass representing a partially ordered set"""

PO = TypeVar("PO", bound=Supports[PartialOrder])

class _Set_PartialOrder_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, Set) \
             and (   len(arg) == 0 \
               or isinstance(peek(arg), Supports[PartialOrder])
               )
    except Exception:
      return False

class Set_PartialOrder(Set[PartialOrder], metaclass=_Set_PartialOrder_Meta): ...

# @typeclass(PartialOrder)
# def is_in_principal_filter_at(p: PO, a: PO, ps: Set[PO]) -> Bool:
#   '''p is in the principal filter at a iff p is in the upper closure of a'''

# @is_in_principal_filter_at.instance(object)
# def _is_in_principal_filter_at(p: PO, a: PO, ps: Set[PO]) -> Bool:
#   return is_in_upper_closure(p, a, ps)

# @typeclass(PartialOrder)
# def is_in_principal_ideal_at(p: PO, a: PO, ps: Set[PO]) -> Bool:
#   '''p is in the principal ideal at a iff p is in the lower closure of a'''

# @is_in_principal_ideal_at.instance(object)
# def _is_in_principal_ideal_at(p: PO, a: PO, ps: Set[PO]) -> Bool:
#   return is_in_lower_closure(p, a, ps)

@typeclass(PartialOrder)
def law_antisymmetric_forAll(a: PO, b: PO) -> Bool:
  '''A binary relation `R` is antisymmetric iff \forall `a`, `b`, `a R b` \land `b R a` \implies `a == b`'''

@law_antisymmetric_forAll.instance(object)
def _law_antisymmetric_forAll_object(a: PO, b: PO) -> Bool:
  return Implies( And( le(a, b)
                     , le(b, a)
                     )
                , eq(a, b)
                )



# class EquivalenceRelation(Preorder):
#   '''Associated type for a typeclass representing an equivalence relation'''

# ER = TypeVar("ER", bound=Supports[EquivalenceRelation])

# @typeclass(EquivalenceRelation)
# def equiv(a: ER, b: ER) -> Bool:
#   '''=='''

# @typeclass(EquivalenceRelation)
# def law_symmetric_forAll(a: ER, b: ER) -> Bool:
#   '''A binary relation `R` is symmetric iff \forall `a`, `b`, `a R b` \implies `b R a`'''

# @law_symmetric_forAll.instance(object)
# def _law_symmetric_forAll_object(a: ER, b: ER) -> Bool:
#   return Implies( equiv(a, b), equiv(b, a) )



class MeetSemilattice(PartialOrder): ...

M = TypeVar("M", bound=Supports[MeetSemilattice])

@typeclass(MeetSemilattice)
def law_meetExists_forAll(a: M, b: M, ps: Optional[Set[M]]) -> Bool:
  '''
  A partial order is a meet semilattice iff \forall `a`, `b` the greatest lower
  bound (meet) of `a` and `b` is some element of the partial order.

  Notes:
    - In a partial order, the meet of `a` and `b` is unique (if it exists).
    - This should be grounds for requiring a function that yields the meet - as
      opposed to what might be suggested by the default law implementation
      below, which has to be relational.
  '''

@law_meetExists_forAll.instance(object)
def _law_meetExists_forAll_object(a: M, b: M, ps: Optional[Set[M]]) -> Bool:
  ensureEnumeration(ps)
  return Or1([ is_greatest_lower_bound(c, a, b, ps)
               for c in ps  # type: ignore
             ])

# @typeclass(MeetSemilattice)
# def meet(left: M, right: M) -> M:
#   """^"""
# @typeclass(MeetSemilattice)
# def meet1(values: Set[M]) -> M:
#   """^ over the collection"""


# class PartialJoinAlgebra(Preorder):
#   """Associated type for a typeclass where join is a partial function"""

# Jp = TypeVar("Jp", bound=Supports[PartialJoinAlgebra])

# @typeclass(PartialJoinAlgebra)
# def joinExists(left: Jp, right: Jp) -> Bool:
#   """\downlollipop"""

# @typeclass(PartialJoinAlgebra)
# def joinExists1(values: Set[Jp]) -> Bool:
#  """\downlollipop"""

# @typeclass(PartialJoinAlgebra)
# def join(left: Jp, right: Jp) -> Jp:
#   """v"""

# @typeclass(PartialJoinAlgebra)
# def join1(values: Set[Jp]) -> Jp:
#   """v"""



class JoinSemilattice(PartialOrder):
# class JoinSemilattice(PartialJoinAlgebra):
  """Associated type for a typeclass representing a join semilattice"""

J = TypeVar("J", bound=Supports[JoinSemilattice])

@typeclass(JoinSemilattice)
def law_joinExists_forAll(a: J, b: J, ps: Optional[Set[J]]) -> Bool:
  '''
  A partial order is a join semilattice iff \forall a, b the least upper
  bound (join) of a and b is some element of the partial order.

  Notes:
    - In a partial order, the join of a and b is unique (if it exists).
    - This should be grounds for requiring a function that yields the join - as
      opposed to what might be suggested by the default law implementation
      below, which has to be relational.
  '''

@law_joinExists_forAll.instance(object)
def _law_joinExists_forAll_object(a: J, b: J, ps: Optional[Set[J]]) -> Bool:
  ensureEnumeration(ps)
  return Or1([ is_least_upper_bound(c, a, b, ps)
               for c in ps  # type: ignore
             ])

# @typeclass(JoinSemilattice)
# def join(left: A, right: A) -> A:
#   """v"""

# @typeclass(JoinSemilattice)
# def join1(values: Set[A]) -> A:
#   """v"""



class BoundedMeetSemilattice(MeetSemilattice, LowerBounded):
  """Associated type for a typeclass representing a bounded meet semilattice"""

BMS = TypeVar("BMS", bound=Supports[BoundedMeetSemilattice])
# BMS = TypeVar("BMS", bound=Supports[MeetSemilattice, LowerBounded])
# BMS = TypeVar("BMS", bound=Union[Supports[MeetSemilattice], Supports[LowerBounded]])

# @typeclass(BoundedMeetSemilattice)
# def min(value: BMS) -> Supports[BoundedMeetSemilattice]:
#   """min"""


# class BoundedJoinSemilattice(JoinSemilattice, UpperBounded):
#   """Associated type for a typeclass representing a bounded join semilattice"""

# BJS = TypeVar("BJS", bound=Supports[BoundedJoinSemilattice])
# BJS = TypeVar("BJS", bound=Supports[JoinSemilattice, UpperBounded])
BJS = TypeVar("BJS", bound=Union[Supports[JoinSemilattice], Supports[UpperBounded]])

# @typeclass(BoundedJoinSemilattice)
# def max(value: BJS) -> Supports[BoundedJoinSemilattice]:
#   """max"""


# class Lattice(MeetSemilattice, JoinSemilattice):
#   """Associated type for a typeclass representing a lattice"""

# L = TypeVar("L", bound=Supports[Lattice])
# L = TypeVar("L", bound=Supports[MeetSemilattice, JoinSemilattice])
L = TypeVar("L", bound=Union[Supports[MeetSemilattice], Supports[JoinSemilattice]])


# class ModularLattice(Lattice):
#   """Associated type for a typeclass representing a modular lattice"""

# ML = TypeVar("ML", bound=Supports[ModularLattice])

# @typeclass(ModularLattice)
# def modularity_antecedent(x: ML, y: ML, z: ML) -> Bool:
#   '''
#   Antecedent of modularity law:
#     \forall x, y, z, x >= z -> x ^ (y v z) = (x ^ y) v z
#   '''

# @modularity_antecedent.instance(object)
# def _modularity_antecedent_object(x: ML, y: ML, z: ML) -> Bool:
#   return ge(x, z)

# @typeclass(ModularLattice)
# def modularity_consequent_LHS(x: ML, y: ML, z: ML) -> Bool:
#   '''
#   LHS of equation in consequent of modularity law:
#     \forall x, y, z, x >= z -> x ^ (y v z) = (x ^ y) v z
#   '''

# @modularity_consequent_LHS.instance(object)
# def _modularity_consequent_LHS_object(x: ML, y: ML, z: ML) -> Bool:
#   return meet(x, join(y, z))

# @typeclass(ModularLattice)
# def modularity_consequent_RHS(x: ML, y: ML, z: ML) -> Bool:
#   '''
#   RHS of equation in consequent of modularity law:
#     \forall x, y, z, x >= z -> x ^ (y v z) = (x ^ y) v z
#   '''

# @modularity_consequent_RHS.instance(object)
# def _modularity_consequent_RHS_object(x: ML, y: ML, z: ML) -> Bool:
#   return join(meet(x, y), z)

# @typeclass(ModularLattice)
# def law_modularity(x: ML, y: ML, z: ML) -> Bool:
#   '''
#   A lattice is modular iff \forall x, y, z:
#     x >= z -> x ^ (y v z) = (x ^ y) v z
#   '''

# @law_modularity.instance(object)
# def _law_modularity_object(x: ML, y: ML, z: ML) -> Bool:
#   return Implies( modularity_antecedent_object(x, y, z)
#                 , _modularity_consequent_LHS_object(x, y, z) == _modularity_consequent_RHS_object(x, y, z)
#                 )



class Nearlattice(BoundedMeetSemilattice): ...

NL = TypeVar("NL", bound=Supports[Nearlattice])

# @typeclass(Nearlattice)
# def joinExists(left: A, right: A) -> Bool:
#   """\downlollipop"""

# @typeclass(Nearlattice)
# def join(left: A, right: A) -> Bool:
#   """v"""

# @typeclass(Nearlattice)
# def join1(values: Set[A]) -> Bool:
#   """v"""

@typeclass(Nearlattice)
def law_upperBoundProperty_forAll(a: NL, b: NL, ps: Optional[Set[NL]]) -> Bool:
  """
  A bounded meet semilattice is a nearlattice iff it has *the upper bound
  property*:
    - every pair of elements that has an upper bound has a *least* upper bound.

  The default implementation of this requires ps be a non-empty enumeration of
  the bounded meet semilattice
  """

@law_upperBoundProperty_forAll.instance(object)
def _law_upperBoundProperty_forAll_object(a: NL, b: NL, ps: Optional[Set[NL]]) -> Bool:
  ensureEnumeration(ps)
  assert isNonempty(ps), f"ps={ps}"  # type: ignore
  return Or1([ Implies( is_upper_bound(p, {a, b})
                      , has_least_upper_bound(a, b, ps)
                      )
               for p in ps  # type: ignore
             ])

@typeclass(Nearlattice)
def law_initialSegment_isA_BoundedLattice_forAll(a: NL, ps: Optional[Set[NL]]) -> Bool:
  """
  A bounded meet semilattice is a nearlattice iff every initial segment (downset,
  principle ideal) is a (bounded) lattice.
  """

@law_initialSegment_isA_BoundedLattice_forAll.instance(object)
def _law_initialSegment_isA_BoundedLattice_forAll_object(a: NL, ps: Optional[Set[NL]]) -> Bool:
  ensureEnumeration(ps)
  assert isNonempty(ps), f"ps={ps}"  # type: ignore
  # We don't have to assert that every preorder law and every partial order
  # law and every ... law hold. We just need to express the extra property that
  # this property expresses *relative to bounded meet semilattices*: in every
  # downset, joins always exist.
  return And1([ Implies( And( le(l, a)
                            , le(r, a)
                            )
                       , Or1([ And( le(j, a)
                                  , is_least_upper_bound(j, l, r)
                                  )
                               for j in ps  # type: ignore
                             ])
                       )
                for l,r in product(ps, repeat=2)  # type: ignore
              ])



class OverridingNearlattice(Nearlattice): ...

ON = TypeVar("ON", bound=Supports[OverridingNearlattice])

@typeclass(OverridingNearlattice)
def is_override(a: ON, left: ON, right: ON, ps: Optional[Set[ON]]) -> Bool:
  """
  a = l <- r (wrt overriding nearlattice ps) iff
    a = lub({ x \in ps : x <= r | (x <= l \land hasJoin(x, r)) })
  See e.g. Cirulis (2011) - Nearlattices with an Overriding Operation.
  """

@is_override.instance(object)
def _is_override_object(a: ON, left: ON, right: ON, ps: Optional[Set[ON]]) -> Bool:
  ensureEnumeration(ps)

  def is_an_upper_bound_of_xs(p: ON) -> Bool:
    return And1([ Implies( Or( le(x, right)
                             , And( le(x, left)
                                  , has_least_upper_bound(x, right, ps)
                                  )
                             )
                         , le(x, p)
                         )
                  for x in ps  # type: ignore
                ])

  a_is_an_upper_bound_of_xs = is_an_upper_bound_of_xs(a)
  a_is_the_lub_of_xs = And1([ Implies( is_an_upper_bound_of_xs(b)
                                     , And( le(b, a)
                                          , le(b, a)
                                          )
                                     )
                              for b in ps  # type: ignore
                            ])
  return And( a_is_an_upper_bound_of_xs, a_is_the_lub_of_xs )

@typeclass(OverridingNearlattice)
def law_override_exists_forAll(left: ON, right: ON, ps: Optional[Set[ON]]) -> Bool:
  """
  In an overriding nearlattice, the override a <- b ()
  """

@law_override_exists_forAll.instance(object)
def _law_override_exists_forAll_object(left: ON, right: ON, ps: Optional[Set[ON]]) -> Bool:
  ensureEnumeration(ps)
  return Or1([ is_override(p, left, right, ps)
               for p in ps  # type: ignore
             ])


class BoundedLattice(MeetSemilattice, JoinSemilattice, LowerBounded, UpperBounded): ...

BL = TypeVar("BL", bound=Supports[BoundedLattice])
# BL = TypeVar("BL", bound=Supports[MeetSemilattice, JoinSemilattice, LowerBounded, UpperBounded])
# BL = TypeVar("BL", bound=Union[Supports[MeetSemilattice], Supports[JoinSemilattice], Supports[LowerBounded], Supports[UpperBounded]])

@typeclass(BoundedLattice)
def complementary(left: BL, right: BL, ps: Optional[Set[BL]]) -> Bool:
  """
  left^{\bot} == right iff
    left ^ right == 0
  and
    left v right == 1
  where 0, 1 are the global lower and upper bounds of the lattice.
  """

@complementary.instance(object)
def _complementary_object(left: BL, right: BL, ps: Optional[Set[BL]]) -> Bool:
  ensureEnumeration(ps)
  return And1([ Implies( And( is_global_lower_bound(b, ps)
                            , is_global_upper_bound(t, ps)
                            )
                       , And( is_greatest_lower_bound(b, left, right, ps)
                            , is_least_upper_bound(t, left, right, ps)
                            )
                       )
                for b,t in product(ps, repeat=2)  # type: ignore
              ])
  # Calls to `global_lower_bound(a, ps)` and `global_upper_bound(a, ps)` cannot
  # return anything meaningful with the current API for `global_lower_bound` in
  # symbolic contexts. The spec for `global_<whatever>_bound` would have to
  # allow for symbolic versions of the function to return
  #   `Tuple[<symbolic type>, Constraint]`
  # bot, top = global_lower_bound(left, ps), global_upper_bound(left, ps)
  # return And( is_greatest_lower_bound(bot, left, right, ps)
  #           , is_least_upper_bound(top, left, right, ps)
  #           )



# class ComplementedLattice(BoundedLattice): ...
class ComplementedLattice(MeetSemilattice, JoinSemilattice, LowerBounded, UpperBounded): ...

CL = TypeVar("CL", bound=Supports[ComplementedLattice])

# @typeclass(ComplementedLattice)
# def complementary(left: CL, right: CL, ps: Optional[Set[P]]) -> Bool:
#   """
#   left^{\bot} == right iff
#     left ^ right == 0
#   and
#     left v right == 1
#   where 0, 1 are the global lower and upper bounds of the lattice.
#   """

# @complementary.instance(object)
# def _complementary_object(left: CL, right: CL, ps: Optional[Set[P]]) -> Bool:
#   bot, top = global_lower_bound(left), global_upper_bound(left)
#   return And( is_greatest_lower_bound(bot, left, right, ps)
#             , is_least_upper_bound(top, left, right, ps)
#             )

@typeclass(ComplementedLattice)
def law_complementExists_forAll(a: CL, ps: Optional[Set[CL]]) -> Bool:
  """
  A lattice is complemented iff every element has at least one complement.
  """

@law_complementExists_forAll.instance(object)
def _law_complementExists_forAll_object(a: CL, ps: Optional[Set[CL]]) -> Bool:
  ensureEnumeration(ps)
  return  Or1([ complementary(a, b, ps)
                for b in ps  # type: ignore
              ])



# class HasOrthocomplementInvolution(BoundedMeetSemilattice):
# class HasOrthocomplementInvolution(MeetSemilattice, LowerBounded):
#  """Associated type for a typeclass representing some kind of orthocomplemented lattice-like structure."""

# HOCI = TypeVar("HOCI", bound=Supports[HasOrthocomplementInvolution])

# @typeclass(HasOrthocomplementInvolution)
# def orthogonal(left: HOCI, right: HOCI) -> Bool:
#   """\bot"""

# @typeclass(HasOrthocomplementInvolution)
# def ortho_inv(value: HOCI) -> HOCI:
#   """^{\bot}"""

# class Orthocomplemented(HasOrthocomplementInvolution):
#   """^{\bot}"""

# O = TypeVar('O', bound=Supports[Orthocomplemented])

# class OrthocomplementedLattice(BoundedLattice): ...

# O = TypeVar('O', bound=Supports[OrthocomplementedLattice])

# @typeclass(OrthocomplementedLattice)
# def is_orthocomplement(a: O, b: O, ps: Optional[Set[O]]):
#   """
#   `a` is the orthocomplement of `b` iff
#    1. `a` and `b` are complementary
#    2. `b` is the orthocomplement of `a`
#    3. `le(a, c)` and `is_orthocomplement(d, c)` imply `le(d, b)`
#   `a` is the unique element that holds these properties wrt `a`
#   """

# def orthocomplemented_law(a: O, b: O):
#   '''An orthocomplementation is an order-reversing involution that maps each element of a lattice to a complement.'''



# # class Orthonearlattice(Nearlattice):
# #   """Associated type for a typeclass representing an orthonearlattice"""

# # @typeclass(Orthonearlattice)
# # def ortho(left: A, right: A) -> Bool:
# #   """\bot"""


# # class OrthomodularNearlattice(Orthonearlattice):
# #   """Associated type for a typeclass representing an orthomodular nearlattice"""
#
# OMN = TypeVar("OMN", bound=Supports[OrthomodularNearlattice])



# class DistributiveLattice(Lattice):
class DistributiveLattice(MeetSemilattice, JoinSemilattice, LowerBounded, UpperBounded): ...

DL = TypeVar("DL", bound=Supports[DistributiveLattice])

# @typeclass(DistributiveLattice)
# def meetDistributesOverJoin_LHS(x: DL, y: DL, z: DL) -> DL:
#   '''
#   Left-hand side of distributive identity:
#     \forall x, y, z, x ^ (y v z) = (x ^ y) v (x ^ z)
#   '''

# @meetDistributesOverJoin_LHS.instance(object)
# def _meetDistributesOverJoin_LHS_object(x: DL, y: DL, z: DL) -> DL:
#   return meet(x, join(y, z))

# @typeclass(DistributiveLattice)
# def meetDistributesOverJoin_RHS(x: DL, y: DL, z: DL) -> DL:
#   '''
#   Right-hand side of distributive identity:
#     \forall x, y, z, x ^ (y v z) = (x ^ y) v (x ^ z)
#   '''

# @meetDistributesOverJoin_RHS.instance(object)
# def _meetDistributesOverJoin_RHS_object(x: DL, y: DL, z: DL) -> DL:
#   return join(meet(x, y), meet(x, z))

# @typeclass(DistributiveLattice)
# def law_meetDistributesOverJoin_forAll(x: DL, y: DL, z: DL) -> Bool:
#   '''
#   A lattice is distributive iff \forall x, y, z:
#     x ^ (y v z) = (x ^ y) v (x ^ z)
#   '''

# @law_meetDistributesOverJoin_forAll.instance(object)
# def _law_meetDistributesOverJoin_forAll_object(x: DL, y: DL, z: DL) -> DL:
#   return _meetDistributesOverJoin_LHS_object(x, y, z) == _meetDistributesOverJoin_RHS_object(x, y, z)

@typeclass(DistributiveLattice)
def law_meetDistributesOverJoin_forAll(x: DL, y: DL, z: DL, ps: Optional[Set[DL]]) -> Bool:
  '''
  A lattice `ps` is distributive iff \forall `x`, `y`, `z`:
    `x ^ (y v z) = (x ^ y) v (x ^ z)`
  '''

@law_meetDistributesOverJoin_forAll.instance(object)
def _law_meetDistributesOverJoin_forAll_object(x: DL, y: DL, z: DL, ps: Optional[Set[DL]]) -> Bool:
  '''
  A lattice `ps` is distributive iff \forall `x`, `y`, `z`:
    `x ^ (y v z) = (x ^ y) v (x ^ z)`

  Translated into a relational style:
  '''
  ensureEnumeration(ps)
  return And1([ Implies( And1([ is_join(yjz    , y  , z  , ps)
                              , is_meet(xmyjz  , x  , yjz, ps)
                              , is_meet(xmy    , x  , y  , ps)
                              , is_meet(xmz    , x  , z  , ps)
                              , is_join(xmyjxmz, xmy, xmz, ps)
                              ])
                       , eq( xmyjz
                           , xmyjxmz
                           )
                       )
                for yjz, xmy, xmz, xmyjz, xmyjxmz in list(product(ps, repeat=5))  # type: ignore
              ])



class BooleanLattice(DistributiveLattice, ComplementedLattice): ...

# BO = TypeVar("BO", bound=Supports[BooleanLattice])

class BooleanNearlattice(Nearlattice): ...

BN = TypeVar("BN", bound=Supports[BooleanNearlattice])

@typeclass(BooleanNearlattice)
def law_initialSegment_isA_ComplementedLattice_forAll(a: BN, ps: Optional[Set[BN]]) -> Bool:
  """
  A nearlattice is Boolean iff every initial segment (downset, principle ideal)
  is a Boolean lattice. A lattice is boolean iff it is both complemented and distributive.
  """

@law_initialSegment_isA_ComplementedLattice_forAll.instance(object)
def _law_initialSegment_isA_ComplementedLattice_forAll_object(a: BN, ps: Optional[Set[BN]]) -> Bool:
  ensureEnumeration(ps)
  assert isNonempty(ps), f"ps={ps}"  # type: ignore
  # We don't have to assert that every preorder law and every partial order
  # law and every ... law hold. We just need to express the extra property that
  # this property expresses *relative to nearlattices*: in every downset
  #  1. every element of the downset x has a relative complement within the downset.
  #  2. meet distributes over join.
  return And1([ Implies( And( le(p, a)
                            , is_global_lower_bound(bot, ps)
                            )
                       , Or1([ And( le(c, a)
                                  , is_least_upper_bound(a, c, p)
                                  )
                               for c in ps  # type: ignore
                             ])
                       )
                for p, bot in product(ps, repeat=2)  # type: ignore
              ])

@typeclass(BooleanNearlattice)
def law_initialSegment_isA_DistributiveLattice_forAll(a: BN, x: BN, y: BN, z: BN, ps: Optional[Set[BN]]) -> Bool:
  """
  A nearlattice is Boolean iff every initial segment (downset, principle ideal)
  is a Boolean lattice. A lattice is boolean iff it is both complemented and distributive.
  """

@law_initialSegment_isA_DistributiveLattice_forAll.instance(object)
def _law_initialSegment_isA_DistributiveLattice_forAll_object(a: BN, x: BN, y: BN, z: BN, ps: Optional[Set[BN]]) -> Bool:
  ensureEnumeration(ps)
  assert isNonempty(ps), f"ps={ps}"  # type: ignore
  # We don't have to assert that every preorder law and every partial order
  # law and every ... law hold. We just need to express the extra property that
  # this property expresses *relative to nearlattices*: in every downset
  #  1. every element of the downset x has a relative complement within the downset.
  #  2. meet distributes over join.
  return And1([ Implies( And1([ le(x, a)
                              , le(y, a)
                              , le(z, a)
                              , is_join(yjz    , y  , z  , ps)
                              , is_meet(xmyjz  , x  , yjz, ps)
                              , is_meet(xmy    , x  , y  , ps)
                              , is_meet(xmz    , x  , z  , ps)
                              , is_join(xmyjxmz, xmy, xmz, ps)
                              ])
                       , eq( xmyjz
                           , xmyjxmz
                           )
                       )
                for yjz, xmy, xmz, xmyjz, xmyjxmz in list(product(ps, repeat=5))  # type: ignore
              ])


class BooleanOverridingNearlattice(OverridingNearlattice, BooleanNearlattice): ...



# A nearlattice of sets is a collection of sets S such that
#  - S is closed under \cap.
#  - (K, L, M \in S) \land (K \cup L \subseteq M) \implies (K \cup M \in S).
# A nearlattice of sets is *Boolean* iff
#  - it is also closed under set difference
# See Cirulis 2011 - Nearlattices with an overriding operation.


class LatticeResiduatedMonoid(Monoid, MeetSemilattice, JoinSemilattice): ...

LRM = TypeVar("LRM", bound=Supports[LatticeResiduatedMonoid])

@typeclass(LatticeResiduatedMonoid)
def is_left_residual(a: LRM, l: LRM, r: LRM, lrms: Optional[Set[LRM]]) -> Bool: ...

@typeclass(LatticeResiduatedMonoid)
def is_right_residual(a: LRM, l: LRM, r: LRM, lrms: Optional[Set[LRM]]) -> Bool: ...

@typeclass(LatticeResiduatedMonoid)
def law_left_residuation(a: LRM, l: LRM, r: LRM, lrms: Optional[Set[LRM]]) -> Bool: ...

@typeclass(LatticeResiduatedMonoid)
def law_right_residuation(a: LRM, l: LRM, r: LRM, lrms: Optional[Set[LRM]]) -> Bool: ...
