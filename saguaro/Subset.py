'''
Module defining an interface (and some instances) for subsets of finite sets
and the Boolean lattice formed by a powerset.
'''

from dataclasses import dataclass
from typing import Generic, TypeVar, Union, Optional
from typing import Collection, Sized, FrozenSet, Set, Tuple, List
from classes import AssociatedType, Supports, typeclass

from functools import cache
from funcy import lmap, walk, lfilter, lmapcat
from itertools import product
import more_itertools

from random import randint, sample, choice#, shuffle, choice, choices

from hypothesis import strategies as st
from hypothesis.strategies import SearchStrategy#, sampled_from

import z3

import saguaro.utilities as SU
import saguaro.Eq        as SE
import saguaro._Boolean  as SB
import saguaro.Order     as SO
import saguaro.Subset    as SS

from saguaro.utilities import A, foldl, peek, fst, snd
from saguaro.utilities import isEmpty, isNonempty, ensureSameLength, ensureNull
from saguaro.utilities import z3Map, SymbolicSort
from saguaro._Boolean import Bool, Constraint, Constraints
from saguaro._Boolean import Not, Not1, \
                             And, And1, Or, Or1, \
                             Implies, Iff, Iff1
from saguaro.Eq import eq, eq1, eq3, elementOf, isContainedBy, neq, neq1, distinct
# from saguaro.Order import P
from saguaro.Order import _enumerate_Preorder, \
                          _Enumeration, _ConcreteEnumeration, _SymbolicEnumeration
from saguaro.Order import le, ge, lt, gt, lt1, gt1, \
                          comparable, is_between, is_in_interval, covers, _covers_object, \
                          is_maximal, is_minimal, \
                          is_upper_bound, is_lower_bound, \
                          is_least_upper_bound, is_least_upper_bound1, \
                          _is_least_upper_bound_object, _is_least_upper_bound1_object, \
                          is_greatest_lower_bound, is_greatest_lower_bound1, \
                          _is_greatest_lower_bound_object, _is_greatest_lower_bound1_object, \
                          is_join, is_join1, is_meet, is_meet1, \
                          has_least_upper_bound, has_least_upper_bound1, \
                          _has_least_upper_bound_object, _has_least_upper_bound1_object, \
                          has_greatest_lower_bound, has_greatest_lower_bound1, \
                          _has_greatest_lower_bound_object, _has_greatest_lower_bound1_object, \
                          has_join, has_join1, has_meet, has_meet1, \
                          global_lower_bound, global_upper_bound, \
                          is_global_lower_bound, is_global_upper_bound, \
                          _is_global_lower_bound_object, _is_global_upper_bound_object, \
                          is_atom, _is_atom_object, \
                          complementary, _complementary_object
# from saguaro.Order import Preorder, PartialOrder, LowerBounded, UpperBounded
# from saguaro.Order import MeetSemilattice, JoinSemilattice
# from saguaro.Order import ComplementedLattice, DistributiveLattice,
from saguaro.Order import BooleanLattice



# UNWRAPPED SUBSETS - functions for manipulating "unwrapped" representations of subsets

def random_nonempty_subset(s: set, k=None) -> list:
  if not isinstance(s, list):  # type: ignore
    pop = list(s)
  else:
    pop = s  # type: ignore

  if k is None:
#     t       = tuple(s)
#     cap     = len(t)
#     return set(sample(population=t, k=size))
    cap     = len(pop)
    size    = randint(1,cap)
  else:
    size=k
  result = sample(population=pop, k=size)
  return result
  # return frozenset(result)

# commented out for now becuase it depends on a feature vector implementation
# def random_interesting_subset(maxAttempts: int, s: set, cap=None, k=None, minSpec=None) -> set:
#   assert maxAttempts > 0
#   assert len(s) > 0
#   assert minSpec is None or minSpec > 0

#   if k is None:
#     if cap is None:
#       cap = len(s)
#     assert cap <= len(s), f"{cap} should be <= {len(s)}"
#     k = randint(1,cap)

#   if minSpec is None:
#     minSpec = 1

#   m     = len(tuple(s)[0])
#   zeroV = FeatureVector.z(m)


#   S = random_nonempty_subset(s, k)
#   attempts = 1
#   while attempts < maxAttempts and FeatureVector.spec(grandFoldl(FeatureVector.meet)(S)) < minSpec:
# #   while attempts < maxAttempts and grandFoldl(FeatureVector.meet)(S) == zeroV:
#     S = randomNonemptySubset(s, k)
#     attempts += 1
#   if grandFoldl(FeatureVector.meet)(S) == zeroV:
#     return None
#   else:
#     return S


def all_subset_vectors(outType=None):
  def f(population_size: int):
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

def is_subseteq_subsetVector(subsetVector_left, subsetVector_right):
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





class Subset(BooleanLattice):
  """Associated type for a typeclass representing finite subsets"""

PS = TypeVar("PS", bound=Supports[Subset])  # "PowerSet"; avoids collision with the `Subset` abbreviation (or typevariable) `SS`

class _Set_Subset_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, Set) \
             and (   len(arg) == 0 \
               or isinstance(peek(arg), Subset)
               )
    except Exception:
      return False

class Set_Subset(Set[Subset], metaclass=_Set_Subset_Meta): ...

# inheriting from Sized should mean that we have to have a __len__ implementation
# @typeclass(Subset)
# def __len__(self: PS) -> int:
#   pass

@typeclass(Subset)
def _universe(value: PS) -> set[A]:
  '''
  #FIXME update docstring when dust settles.
  Returns the universe of possible values associated with this value as some
  kind of collection (probably a python set or tuple). This is the internal
  representation used by `value` (or very close to it) - hence why it is
  `set[A]`.
  '''

@typeclass(Subset)
def _subset(value: PS) -> Set:
  '''
  Returns a concrete python Set representing the actual 'payload' of
  `value`. Note that while for concrete representations this will be a
  collection of concrete values, for a symbolic representation this will be
  something symbolic.
  '''

@typeclass(Subset)
def _consistent_subset_universe(value: PS) -> bool:
  '''Indicates whether `value`'s `subset` is consistent with `universe`.'''

@typeclass(Subset)
def _validBinOpRelVals(subset: PS, left: PS, right: PS) -> bool: ...

@_validBinOpRelVals.instance(object)
def _validBinOpRelVals_object(subset: PS, left: PS, right: PS) -> bool:
  argsValid      = _consistent_subset_universe(subset) and \
                   _consistent_subset_universe(left) and \
                   _consistent_subset_universe(right)
  universesValid = _universe(subset) == _universe(left) == _universe(right)
  if not argsValid:
    if not _consistent_subset_universe(subset):
      raise Exception(f"Inconsistent subset vs. universe: {subset}")
    if not _consistent_subset_universe(left):
      raise Exception(f"Inconsistent subset vs. universe: {left}")
    if not _consistent_subset_universe(right):
      raise Exception(f"Inconsistent subset vs. universe: {right}")
  if not universesValid:
    if not (_universe(subset) == _universe(left)):
      raise Exception(f"Universes not equal: {_universe(left)} != {_universe(subset)}\nleft={left}\nright={subset}")
    if not (_universe(right) == _universe(left)):
      raise Exception(f"Universes not equal: {_universe(right)} != {_universe(right)}\nleft={left}\nright={right}")
  return argsValid and universesValid

@typeclass(Subset)
def _validBinOpArgs(left: PS, right: PS) -> bool: ...

@_validBinOpArgs.instance(object)
def _validBinOpArgs_object(left: PS, right: PS) -> bool:
  argsValid      = _consistent_subset_universe(left) and \
                   _consistent_subset_universe(right)
  universesValid = _universe(left) == _universe(right)
  if not argsValid:
    if not _consistent_subset_universe(left):
      raise Exception(f"Inconsistent subset vs. universe: {left}")
    if not _consistent_subset_universe(right):
      raise Exception(f"Inconsistent subset vs. universe: {right}")
  if not universesValid:
    raise Exception(f"Universes not equal: {_universe(left)} != {_universe(right)}\nleft={left}\nright={right}")
  return argsValid and universesValid

@typeclass(Subset)
def _validContainerOpRelVals(subset: PS, values: Set[PS]) -> bool: ...

@_validContainerOpRelVals.instance(object)
def _validContainerOpRelVals_object(subset: PS, values: Set[PS]) -> bool:
  argsValid      = _consistent_subset_universe(subset) and \
                   all([ _consistent_subset_universe(v)
                         for v in values
                       ])
  us             = _universe(subset)
  universesValid = len(values) == 0 or \
                   all([ _universe(v) == us
                         for v in values
                       ])
  return argsValid and universesValid

@typeclass(Subset)
def _validContainerOpArg(values: Set[PS]) -> bool: ...

@_validContainerOpArg.instance(delegate=Set_Subset)
def _validContainerOpArg_object(values: Set[PS]) -> bool:
  if isEmpty(values):
    return True
  argsValid      = all([ _consistent_subset_universe(v)
                         for v in values
                       ])
  u              = _universe(peek(values))
  universesValid = len(values) == 0 or \
                   all([ _universe(v) == u
                         for v in values
                       ])
  return argsValid and universesValid

@eq.instance(Subset)
def _eq_Subset(left: PS, right: PS) -> Bool:
  assert _validBinOpArgs(left, right), f"left={left}\nright={right}"
  return And1([ Iff( has_element(left , p)
                   , has_element(right, p)
                   )
                for p in _universe(left)
              ])

@eq1.instance(delegate=Set_Subset)
def _eq1_Subset(values: Set[PS]) -> Bool:
  assert _validContainerOpArg(values), f"values={values}"
  assert isNonempty(values), f"values={values}"
  v0 = peek(values)
  return And1([ eq(v, v0)
                for v in values
              ])

# @has_meet1.instance(delegate=Set_Subset)
# def _has_meet1_Subset(s: Set[PS]) -> Bool:
#   return has_greatest_lower_bound1(s)

@typeclass(Subset)
def is_empty(subset: PS) -> Bool: ...

@is_empty.instance(object)
def _is_empty_object(subset: PS) -> Bool:
  return eq(subset, global_lower_bound(subset, None))

@typeclass(Subset)
def is_nonempty(subset: PS) -> Bool: ...

@is_nonempty.instance(object)
def _is_nonempty_object(subset: PS) -> Bool:
  return Not(is_empty(subset))

@typeclass(Subset)
def is_universe(subset: PS) -> Bool: ...

@is_universe.instance(object)
def _is_universe_object(subset: PS) -> Bool:
  return eq(subset, global_upper_bound(subset, None))

@typeclass(Subset)
def has_element(subset: PS, value: A) -> Bool: ...

@typeclass(Subset)
def missing_element(subset: PS, value: A) -> Bool: ...

@missing_element.instance(object)
def _missing_element_object(subset: PS, value: A) -> Bool:
  return Not(has_element(subset, value))

@typeclass(Subset)
def has_exactly_k_elements(subset: PS, k: int) -> Bool: ...

@typeclass(Subset)
def has_atLeast_k_elements(subset: PS, k: int) -> Bool: ...

@typeclass(Subset)
def has_atMost_k_elements(subset: PS, k: int) -> Bool: ...

@typeclass(Subset)
def is_intersection(subset: PS, left: PS, right: PS) -> Bool: ...

@typeclass(Subset)
def is_union(subset: PS, left: PS, right: PS) -> Bool: ...

@typeclass(Subset)
def is_difference(subset: PS, left: PS, right: PS) -> Bool: ...

@typeclass(Subset)
def is_subseteq(left: PS, right: PS) -> Bool: ...

@is_subseteq.instance(object)
def _is_subseteq_object(left: PS, right: PS) -> Bool:
  return le(left, right)

@typeclass(Subset)
def is_supseteq(left: PS, right: PS) -> Bool: ...

@is_supseteq.instance(object)
def _is_supseteq_object(left: PS, right: PS) -> Bool:
  return ge(left, right)


@dataclass(frozen=True)
class NaiveSubset(Subset, Generic[A]):
  '''
  Naive implementation of the Subset typeclass: a wrapper for two Python sets.
  '''

  subset: set[A]   # concrete
  universe: set[A] # concrete

  def __hash__(self):
    return hash((frozenset(self.subset), frozenset(self.universe)))

  def unwrap(self) -> Tuple[set[A], set[A]]:
    return (self.subset, self.universe)

  # Smart constructors + helpers

  @staticmethod
  def _consistent_subset_universe(subset: set[A], universe: set[A]) -> bool:
    return all([each in universe for each in subset])

  # @staticmethod
  # def _consistent_universe_enumeration(universe: set[A], enumeration: _ConcreteEnumeration[A]) -> bool:
  #   return NaiveSubset.same_universes(enumeration.values)

  # def _ensurePsIsNull(ps: Optional[Set['NaiveSubset[A]']]) -> bool:
  #   return ensureNull(ps, f"Explicitly passing an entire powerset is impractical and unnecessary for NaiveSubset[A].")

  @staticmethod
  def mk(subset: set[A], universe: set[A]) -> 'NaiveSubset[A]':
    # Return type is a quoted string (until https://peps.python.org/pep-0649/ or something similar is accepted)
    # because of python's half-baked annotation evaluation order: cf
    #   - https://peps.python.org/pep-0563/#enabling-the-future-behavior-in-python-3-7
    #   - https://stackoverflow.com/a/51444348
    if not isinstance(universe, set):
      raise Exception(f"universe must be a set, got value of type '{type(universe)}': '{universe}'")
    if not isinstance(subset, set):
      raise Exception(f"subset must be a set, got value of type '{type(subset)}': '{subset}'")
    assert NaiveSubset._consistent_subset_universe(subset, universe)
    return NaiveSubset(subset, universe)

  # FIXME
  # @staticmethod
  # def mk1(subsetVector: SubsetVector[A]) -> 'NaiveSubset[A]':
  #   pass

  # @staticmethod
  # def mk2(symbolicSubsetVector: SymbolicVectorSubset[A]) -> 'NaiveSubset[A]':
  #   pass

  # @staticmethod
  # def mk3(symbolicSubset: SymbolicSubset[A]) -> 'NaiveSubset[A]':
  #   pass

  # Obligatory function because Subset is an instance of Sized
  def __len__(self: 'NaiveSubset[A]') -> int:
   return len(self.subset)

  #FIXME consider declaring NaiveSubset an instance of `Container`
  def __contains__(self: 'NaiveSubset[A]', a) -> bool:
    return a in self.subset

  # Obligatory functions (+ helpers) because Subset is an instance of Eq
  @staticmethod
  def same_universe(left: 'NaiveSubset[A]', right: 'NaiveSubset[A]') -> bool:
    return left.universe == right.universe

  @staticmethod
  def same_subset(left: 'NaiveSubset[A]', right: 'NaiveSubset[A]') -> bool:
    return left.subset == right.subset

  @staticmethod
  def same_universes(values: Set['NaiveSubset[A]']) -> bool:
    values_seq = list(values)
    u0         = values_seq[0].universe
    return all([v.universe == u0 for v in values_seq])

  @staticmethod
  def same_subsets(values: set['NaiveSubset[A]']) -> bool:
    values_seq = list(values)
    s0         = values_seq[0].subset
    return all([v.subset == s0 for v in values_seq])

  # @meet.instance(NaiveSubset[A])
  @staticmethod
  def _meet_NaiveSubset(left: 'NaiveSubset[A]', right: 'NaiveSubset[A]') -> 'NaiveSubset[A]':
    assert _validBinOpArgs_NaiveSubset(left, right), f"left={left}\nright={right}"
    return NaiveSubset(left.subset.intersection(right.subset), left.universe)

  # @meet1.instance(NaiveSubset[A])
  @staticmethod
  def _meet1_NaiveSubset(values: Set['NaiveSubset[A]']) -> 'NaiveSubset[A]':
    assert _validContainerOpArg_NaiveSubset(values), f"values={values}"
    if len(values) == 0:
      return NaiveSubset.mk(set(), set())
    else:
      v0               = peek(values)
      universe_raw     = v0.universe  # type: ignore
      subsets_raw      = lmap(lambda ns: ns.subset, values)
      intersection_raw = foldl(lambda a, b: a.intersection(b), universe_raw)(subsets_raw)  # type: ignore
      return NaiveSubset.mk(intersection_raw, universe_raw)

  # Obligatory: Subset is an instance of PartialJoinAlgebra
  # @joinExists.instance(NaiveSubset[A])
  # @staticmethod
  # def _joinExists_NaiveSubset(left: 'NaiveSubset[A]', right: 'NaiveSubset[A]') -> bool:
    # assert _validBinOpArgs_NaiveSubset(left, right), f"left={left}\nright={right}"
    # return #FIXME

  # @join.instance(NaiveSubset[A])
  @staticmethod
  def _join_NaiveSubset(left: 'NaiveSubset[A]', right: 'NaiveSubset[A]') -> 'NaiveSubset[A]':
    assert _validBinOpArgs_NaiveSubset(left, right), f"left={left}\nright={right}"
    return NaiveSubset(left.subset.union(right.subset), left.universe)

  # @join1.instance(NaiveSubset[A])
  @staticmethod
  def _join1_NaiveSubset(values: Set['NaiveSubset[A]']) -> 'NaiveSubset[A]':
    assert _validContainerOpArg_NaiveSubset(values), f"values={values}"
    if len(values) == 0:
      return NaiveSubset.mk(set(), set())
    else:
      v0               = peek(values)
      universe_raw     = v0.universe  # type: ignore
      subsets_raw = lmap(lambda ns: ns.subset, values)
      union_raw   = foldl(lambda a, b: a.union(b), set())(subsets_raw)  # type: ignore
      return NaiveSubset.mk(union_raw, universe_raw)

  @staticmethod
  def _global_upper_bound_NaiveSubset(subset: 'NaiveSubset[A]') -> 'NaiveSubset[A]':
    return NaiveSubset(subset.universe, subset.universe)

  @staticmethod
  def _global_lower_bound_NaiveSubset(subset: 'NaiveSubset[A]') -> 'NaiveSubset[A]':
    return NaiveSubset(set(), subset.universe)

  @staticmethod
  def _intersection_NaiveSubset(left: 'NaiveSubset[A]', right: 'NaiveSubset[A]') -> 'NaiveSubset[A]':
    assert _validBinOpArgs_NaiveSubset(left, right), f"left={left}\nright={right}"
    return NaiveSubset.mk(left.subset.intersection(right.subset), left.universe)

  @staticmethod
  def _union_NaiveSubset(left: 'NaiveSubset[A]', right: 'NaiveSubset[A]') -> 'NaiveSubset[A]':
    assert _validBinOpArgs_NaiveSubset(left, right), f"left={left}\nright={right}"
    return NaiveSubset.mk(left.subset.union(right.subset), left.universe)

  @staticmethod
  def _difference_NaiveSubset(left: 'NaiveSubset[A]', right: 'NaiveSubset[A]') -> 'NaiveSubset[A]':
    assert _validBinOpArgs_NaiveSubset(left, right), f"left={left}\nright={right}"
    return NaiveSubset.mk(left.subset.difference(right.subset), left.universe)

  # @staticmethod
  # def _cartesian_product_NaiveSubset(left: 'NaiveSubset[A]', right: 'NaiveSubset[A]') -> 'NaiveSubset[A]':
  #   assert _validBinOpArgs_NaiveSubset(left, right), f"left={left}\nright={right}"
  #   return NaiveSubset( set(product( left.subset  # type: ignore
  #                                  , right.subset
  #                                  ))
  #                     , set(product( left.universe  # type: ignore
  #                                  , right.universe
  #                                  ))
  #                     )

  # @staticmethod
  # def _cartesian_product_NaiveSubset(left: Set['NaiveSubset[A]'], right: Set['NaiveSubset[A]']) -> Set[Tuple['NaiveSubset[A]', 'NaiveSubset[A]']]:
  #   return list(product(left, right))

  @staticmethod
  def _enumerate_atoms_from_universe(universe: set[A]) -> set['NaiveSubset[A]']:
    return set({ NaiveSubset( {s}
                            , universe
                            )
                 for s in universe
               })

  @staticmethod
  def _enumerate_universe_from_atoms(atoms: Set['NaiveSubset[A]']) -> set[A]:
    non_singletons = lfilter( lambda a: len(a.subset) != 1
                            , atoms
                            )
    assert len(non_singletons) == 0, f"{non_singletons}"

    universe = foldl( lambda a, b: a.union(b)
                    , set()  # type: ignore
                    )( lmap( lambda ns: ns.subset
                           , atoms
                           )
                     )
    return universe

  # @staticmethod
  # def _enumerate_powerset_from_universe(universe: set[A]) -> _ConcreteEnumeration['NaiveSubset[A]']:
  #   ps = frozenset(map( frozenset  # type: ignore
  #                     , more_itertools.powerset(universe)
  #                     ))
  #   return _ConcreteEnumeration(ps)



# NS = TypeVar('NS', bound=NaiveSubset)

class _Set_NaiveSubset_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, Set) \
             and (   len(arg) == 0 \
                   or all([isinstance(arg, NaiveSubset)])
               # or isinstance(peek(arg), NaiveSubset)
               )
    except Exception:
      return False

class Set_NaiveSubset(Set[NaiveSubset], metaclass=_Set_NaiveSubset_Meta): ...

class _FrozenSet_NaiveSubset_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, FrozenSet) \
             and (   len(arg) == 0 \
                   or all([isinstance(arg, NaiveSubset)])
               # or isinstance(peek(arg), NaiveSubset)
               )
    except Exception:
      return False

class FrozenSet_NaiveSubset(FrozenSet[NaiveSubset], metaclass=_FrozenSet_NaiveSubset_Meta): ...

def _strategy_NaiveSubset_int(num_elements: int = 3) -> SearchStrategy[NaiveSubset[int]]:
  ps = _NaiveSubset_PS_int(num_elements)
  return st.just(choice(list(ps)))
  # return st.builds( NaiveSubset
  #                 , subset = st.sets( elements = st.integers(min_value = 0, max_value = num_elements - 1)
  #                                   , min_size = 0
  #                                   , max_size = num_elements + 1
  #                                   )
  #                 , universe = st.just(set(range(num_elements)))
  #                 )

@cache
def _NaiveSubset_PS_int(num_elements: int = 3) -> Set[NaiveSubset[int]]:
  u = set(range(num_elements))

  def mk(subset: set[int]) -> NaiveSubset[int]:
    return NaiveSubset(subset, universe = u)

  ps = map( set
          , more_itertools.powerset(u)
          )

  return set(map( mk  # type: ignore
                , ps
                )
            )

# @cache
def _strategy_NaiveSubset_PS_int(num_elements: int = 3) -> SearchStrategy[Set[NaiveSubset[int]]]:
  return st.just(_NaiveSubset_PS_int(num_elements))
  # u = set(range(num_elements))

  # def mk(subset: set[int]) -> NaiveSubset[int]:
  #   return NaiveSubset(subset, universe = u)

  # ps = map( set
  #         , more_itertools.powerset(u)
  #         )

  # return st.just(set(map( mk  # type: ignore
  #                       , ps
  #                       )
  #                   )
  #               )

# def _strategy_NaiveSubset_PS_bot_int(num_elements: int = 3) -> SearchStrategy[NaiveSubset[int]]:
#   empty: set[int] = set()
#   return st.just(NaiveSubset(empty, set(range(num_elements))))

# def _strategy_NaiveSubset_PS_top_int(num_elements: int = 3) -> SearchStrategy[NaiveSubset[int]]:
#   return st.just(NaiveSubset(set(range(num_elements)), set(range(num_elements))))

def _strategy_NaiveSubset_Set_int(num_elements: int = 3) -> SearchStrategy[Set[NaiveSubset[int]]]:
  ps = _NaiveSubset_PS_int(num_elements)

  return st.just(random_nonempty_subset(ps))
  # u = set(range(num_elements))

  # ps = lmap( set
  #          , more_itertools.powerset(u)
  #          )

  # collection = random_nonempty_subset(ps)

  # def mk(subset: set[int]) -> NaiveSubset[int]:
  #   return NaiveSubset(subset, universe = u)

  # return st.just(set(map( mk
  #                       , collection
  #                       )
  #                   )
  #               )

@eq.instance(NaiveSubset)
def _eq_NaiveSubset(left: NaiveSubset[A], right: Subset) -> Bool:
  if isinstance(right, NaiveSubset):
    return NaiveSubset.same_subset(left, right) and NaiveSubset.same_universe(left, right)
  else:
    return _eq_Subset(left, right)

@eq1.instance(delegate=Set_NaiveSubset)
def _eq1_NaiveSubset(values: Set[NaiveSubset[A]]) -> Bool:
  if all([isinstance(v, NaiveSubset) for v in values]):
    return NaiveSubset.same_subsets(values) and NaiveSubset.same_universes(values)
  else:
    return _eq1_Subset(values)

# Obligatory: Subset is an instance of Preorder

# @is_cartesian_product.instance(NaiveSubset)
# def _is_cartesian_product_NaiveSubset(product: Set[Tuple[NaiveSubset[A], NaiveSubset[A]]], left: Set[NaiveSubset[A]], right: Set[NaiveSubset[A]]) -> bool:
#   return product == NaiveSubset._cartesian_product_NaiveSubset(left, right)

@le.instance(NaiveSubset)
def _le_NaiveSubset(left: NaiveSubset[A], right: NaiveSubset[A]) -> bool:
  assert _validBinOpArgs_NaiveSubset(left, right), f"left={left}\nright={right}"
  # NB the line below is fine because ".issubset" tests <= and NOT strict <
  return left.subset.issubset(right.subset)

@ge.instance(NaiveSubset)
def _ge_NaiveSubset(left: NaiveSubset[A], right: NaiveSubset[A]) -> bool:
  assert _validBinOpArgs_NaiveSubset(left, right), f"left={left}\nright={right}"
  return le(right, left)

# #FIXME redundant with default implementation
# @lt.instance(NaiveSubset)
# def _lt_NaiveSubset(left: NaiveSubset[A], right: NaiveSubset[A]) -> bool:
#   assert _validBinOpArgs_NaiveSubset(left, right), f"left={left}\nright={right}"
#   return le(left, right) and not eq(left, right)

# #FIXME redundant with default implementation
# @gt.instance(NaiveSubset)
# def _gt_NaiveSubset(left: NaiveSubset[A], right: NaiveSubset[A]) -> bool:
#   assert _validBinOpArgs_NaiveSubset(left, right), f"left={left}\nright={right}"
#   return lt(right, left)

# @_enumerate_Preorder.instance(NaiveSubset)
# def _enumerate_Preorder_NaiveSubset(subset: NaiveSubset[A]) -> _Enumeration[A]:
#   '''
#   Generates the entire powerset associated with `subset`
#   '''
#   return subset.enumeration

@_enumerate_Preorder.instance(NaiveSubset)
def _enumerate_Preorder_NaiveSubset(subset: NaiveSubset[A]) -> _ConcreteEnumeration[NaiveSubset[A]]:
  '''
  Generates the entire powerset associated with `subset`
  '''
  universe = subset.universe
  subsets  = map( set
                , more_itertools.powerset(universe)
                )

  def _mk(s: set[A]) -> NaiveSubset[A]:
    return NaiveSubset(subset=s, universe=universe)

  return _ConcreteEnumeration.freeze(set(lmap(_mk, subsets)))

# @_enumerate_Preorder.instance(NaiveSubset)
# def _enumerate_Preorder_NaiveSubset(atoms: Set[NaiveSubset[A]]) -> Set[NaiveSubset[A]]:
#   '''
#   Generates an entire powerset given a collection of atoms (singletons used to generate the powerset).
#   '''
#   universe = NaiveSubset._enumerate_universe_from_atoms(atoms)
#   subsets  = more_itertools.powerset(universe)

#   def _mk(s: set[A]) -> NaiveSubset[A]:
#     return NaiveSubset(subset=s, universe=universe)

#   return lmap(_mk, subsets)


# Obligatory: Subset is an instance of MeetSemilattice #FIXME move this line downwards appropriately

@is_greatest_lower_bound.instance(NaiveSubset)
def _is_greatest_lower_bound_NaiveSubset( a: NaiveSubset[A]
                                        , left: NaiveSubset[A]
                                        , right: NaiveSubset[A]
                                        , ps: Optional[Set[NaiveSubset[A]]]
                                        ) -> bool:
  assert _validBinOpArgs_NaiveSubset(left, right), f"left={left}\nright={right}"
  assert _validBinOpArgs_NaiveSubset(left, a), f"left={left}\na={a}"
  if ps is None:
    actual_meet   = NaiveSubset._meet_NaiveSubset(left, right) # FIXME update call if necessary whenever the dust settles on a functional interface
    eq_constraint = eq(actual_meet, a)
    return eq_constraint
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert _validContainerOpRelVals(left, ps), f"left={left}\nps={ps}"
    assert isNonempty(ps), f"ps={ps}"
    return _is_greatest_lower_bound_object(a, left, right, ps)

@has_greatest_lower_bound.instance(NaiveSubset)
def _has_greatest_lower_bound_NaiveSubset( left: NaiveSubset[A]
                                         , right: NaiveSubset[A]
                                         , ps: Optional[Set[NaiveSubset[A]]]
                                         ) -> Constraint:
  assert _validBinOpArgs_NaiveSubset(left, right)
  if ps is None:
    return True  # NaiveSubset._meet_NaiveSubset should be total
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert _validContainerOpRelVals(left, ps), f"left={left}\nps={ps}"
    assert _validContainerOpArg(ps), f"ps={ps}"
    return _has_greatest_lower_bound_object(left, right, ps)

@is_greatest_lower_bound1.instance(NaiveSubset)
def _is_greatest_lower_bound1_NaiveSubset( a: NaiveSubset[A]
                                         , s: Set[NaiveSubset[A]]
                                         , ps: Optional[Set[NaiveSubset[A]]]
                                         ) -> bool:
  assert _validContainerOpRelVals_NaiveSubset(a, s), f"a={a}\ns={s}"
  if ps is None:
    actual_meet = NaiveSubset._meet1_NaiveSubset(s)  # FIXME update call if necessary whenever the dust settles on a functional interface
    eq_constraint = eq(actual_meet, a)
    return eq_constraint
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert _validContainerOpRelVals(a, ps), f"a={a}\nps={ps}"
    assert isNonempty(ps), f"ps={ps}"
    assert isNonempty(s), f"s={s}\nps={ps}"
    assert _validContainerOpArg(ps), f"ps={ps}"
    assert _validContainerOpArg(s), f"s={s}"
    assert all([_validContainerOpRelVals(each, ps) for each in s]), f"s={s}\nps={ps}"
    return _is_greatest_lower_bound1_object(a, s, ps)

@has_greatest_lower_bound1.instance(delegate=Set_NaiveSubset)
def _has_greatest_lower_bound1_NaiveSubset( s: Set[NaiveSubset[A]]
                                          , ps: Optional[Set[NaiveSubset[A]]]
                                          ) -> bool:
  if ps is None:
    return True  # NaiveSubset._meet1_NaiveSubset should be total
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert isNonempty(ps), f"ps={ps}"
    assert isNonempty(s), f"s={s}"
    assert _validContainerOpArg(ps), f"ps={ps}"
    assert _validContainerOpArg(s), f"s={s}"
    assert all([_validContainerOpRelVals(each, ps) for each in s]), f"s={s}\nps={ps}"
    return _has_greatest_lower_bound1_object(s, ps)

# Obligatory: Subset is an instance of JoinSemilattice #FIXME move this line downwards appropriately

@is_least_upper_bound.instance(NaiveSubset)
def _is_least_upper_bound_NaiveSubset( a: NaiveSubset[A]
                                     , left: NaiveSubset[A]
                                     , right: NaiveSubset[A]
                                     , ps: Optional[Set[NaiveSubset[A]]]
                                     ) -> bool:
  assert _validBinOpArgs_NaiveSubset(left, right), f"left={left}\nright={right}"
  assert _validBinOpArgs_NaiveSubset(left, a), f"left={left}\na={a}"
  if ps is None:
    actual_join = NaiveSubset._join_NaiveSubset(left, right) # FIXME update call if necessary whenever the dust settles on a functional interface
    eq_constraint = eq(actual_join, a)
    return eq_constraint
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert _validContainerOpRelVals(left, ps), f"left={left}\nps={ps}"
    assert isNonempty(ps), f"ps={ps}"
    return _is_least_upper_bound_object(a, left, right, ps)

@has_least_upper_bound.instance(NaiveSubset)
def _has_least_upper_bound_NaiveSubset(left: NaiveSubset[A], right: NaiveSubset[A], ps: Optional[Set[NaiveSubset[A]]]) -> bool:
  assert _validBinOpArgs_NaiveSubset(left, right)
  if ps is None:
    return True  # NaiveSubset._meet_NaiveSubset should be total
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert _validContainerOpRelVals(left, ps), f"left={left}\nps={ps}"
    assert isNonempty(ps), f"ps={ps}"
    return _has_least_upper_bound_object(left, right, ps)

@is_least_upper_bound1.instance(NaiveSubset)
def _is_least_upper_bound1_NaiveSubset( a: NaiveSubset[A]
                                      , s: Set[NaiveSubset[A]]
                                      , ps: Optional[Set[NaiveSubset[A]]]
                                      ) -> bool:
  assert _validContainerOpRelVals_NaiveSubset(a, s), f"a={a}\ns={s}"
  if ps is None:
    actual_join = NaiveSubset._join1_NaiveSubset(s)  # FIXME update call if necessary whenever the dust settles on a functional interface
    eq_constraint = eq(actual_join, a)
    return eq_constraint
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert _validContainerOpRelVals(a, ps), f"a={a}\nps={ps}"
    assert isNonempty(ps), f"ps={ps}"
    assert isNonempty(s), f"s={s}\nps={ps}"
    assert _validContainerOpArg(ps), f"ps={ps}"
    assert _validContainerOpArg(s), f"s={s}"
    assert all([_validContainerOpRelVals(each, ps) for each in s]), f"s={s}\nps={ps}"
    return _is_least_upper_bound1_object(a, s, ps)

@covers.instance(NaiveSubset)
def _covers_NaiveSubset(c: NaiveSubset[A], a: NaiveSubset[A], ps: Optional[Set[NaiveSubset[A]]]) -> bool:
  assert _validBinOpArgs(c, a), f"c={c}, a={a}"
  if ps is None:
    atoms = NaiveSubset._enumerate_atoms_from_universe(c.universe)
    cover_con = And( distinct(c, a)
                   , Or1([ eq( a
                             , NaiveSubset._difference_NaiveSubset(c, atom)
                             )
                           for atom in atoms
                         ])
                   )
    return cover_con
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert _validContainerOpRelVals(c, ps), f"c={c}\nps={ps}"
    assert isNonempty(ps), f"ps={ps}"
    return _covers_object(c, a, ps)


#LowerBounded

@global_lower_bound.instance(NaiveSubset)
def _global_lower_bound_NaiveSubset(p: NaiveSubset[A], ps: Optional[Set[NaiveSubset[A]]]) -> NaiveSubset[A]:
  if ps is None:
    return NaiveSubset._global_lower_bound_NaiveSubset(p)
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    _validContainerOpRelVals(p, ps), f"p={p}\nps={ps}"
    glb = lfilter( lambda q: is_greatest_lower_bound1(q, ps, ps)
                 , ps
                 )
    assert len(glb) == 1, f"p={p}\nps={ps}\nglb={glb}"
    return glb[0]

@is_global_lower_bound.instance(NaiveSubset)
def _is_global_lower_bound_NaiveSubset(p: NaiveSubset[A], ps: Optional[Set[NaiveSubset[A]]]) -> bool:
  if ps is None:
    bot_constant = NaiveSubset._global_lower_bound_NaiveSubset(p)  # FIXME update call if necessary whenever the dust settles on a functional interface
    return eq(bot_constant, p)
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    return _is_global_lower_bound_object(p, ps)

@is_atom.instance(NaiveSubset)
def _is_atom_NaiveSubset(p: NaiveSubset[A], ps: Optional[Set[NaiveSubset[A]]]) -> bool:
  if ps is None:
    return len(p.subset) == 1
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    return _is_atom_object(p, ps)

#UpperBounded

@global_upper_bound.instance(NaiveSubset)
def _global_upper_bound_NaiveSubset(p: NaiveSubset[A], ps: Optional[Set[NaiveSubset[A]]]) -> NaiveSubset[A]:
  if ps is None:
    return NaiveSubset._global_upper_bound_NaiveSubset(p)
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    _validContainerOpRelVals(p, ps), f"p={p}\nps={ps}"
    lub = lfilter( lambda q: is_least_upper_bound1(q, ps, ps)
                 , ps
                 )
    assert len(lub) == 1, f"p={p}\nps={ps}\nlub={lub}"
    return lub[0]

@is_global_upper_bound.instance(NaiveSubset)
def _is_global_upper_bound_NaiveSubset(p: NaiveSubset[A], ps: Optional[Set[NaiveSubset[A]]]) -> bool:
  if ps is None:
    top_constant = NaiveSubset._global_upper_bound_NaiveSubset(p)  # FIXME update call if necessary whenever the dust settles on a functional interface
    return eq(top_constant, p)
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    return _is_global_upper_bound_object(p, ps)

# # Obligatory: Subset is an instance of BoundedMeetSemilattice
# @min.instance(NaiveSubset)
# def _min_NaiveSubset(value: NaiveSubset[A]) -> NaiveSubset[A]:
#   return #FIXME

# # Obligatory: Subset is an instance of BoundedJoinSemilattice
# @max.instance(NaiveSubset)
# def _max_NaiveSubset(value: NaiveSubset[A]) -> NaiveSubset[A]:
#   return #FIXME

# # ortho
# @ortho.instance(NaiveSubset)
# def _ortho_NaiveSubset(left: NaiveSubset[A], right: NaiveSubset[A]) -> NaiveSubset[A]:
#   assert _validBinOpArgs_NaiveSubset(left, right), f"left={left}\nright={right}"
#   return #FIXME


# Obligatory: NaiveSubset is an instance of ComplementedLattice
# technically there's a default implementation we can use
@complementary.instance(NaiveSubset)
def _complementary_NaiveSubset(left: NaiveSubset[A], right: NaiveSubset[A], ps: Optional[Set[NaiveSubset[A]]]) -> bool:
  assert _validBinOpArgs_NaiveSubset(left, right), f"left={left}\nright={right}"
  if ps is None:
    top = NaiveSubset._global_upper_bound_NaiveSubset(left)
    bot = NaiveSubset._global_lower_bound_NaiveSubset(left)
    return And( eq(NaiveSubset._meet_NaiveSubset(left, right), bot)
              , eq(NaiveSubset._join_NaiveSubset(left, right), top)
              )
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert _validContainerOpRelVals(left, ps)
    return _complementary_object(left, right, ps)

# Obligatory: Subset
#FIXME when you are satisfied that `_validBinOpRelVals` ought to be `Subset` typeclass method
#replace existing references in the `NaiveSubset` implementation to this specific instance.
#Ditto for the three methods below this one.
@_validBinOpRelVals.instance(NaiveSubset)
def _validBinOpRelVals_NaiveSubset(subset: NaiveSubset[A], left: Subset, right: Subset) -> bool:
# def _validBinOpRelVals_NaiveSubset(subset: NaiveSubset[A], left: NaiveSubset[A], right: NaiveSubset[A]) -> bool:
  if isinstance(left, NaiveSubset) and isinstance(right, NaiveSubset):
    return NaiveSubset.same_universe(left, right) and NaiveSubset.same_universe(subset, left)
  else:
    return _validBinOpRelVals_object(subset, left, right)

@_validBinOpArgs.instance(NaiveSubset)
def _validBinOpArgs_NaiveSubset(left: NaiveSubset[A], right: Subset) -> bool:
  if isinstance(right, NaiveSubset):
    return NaiveSubset.same_universe(left, right)
  else:
    return _validBinOpArgs_object(left, right)

@_validContainerOpRelVals.instance(NaiveSubset)
def _validContainerOpRelVals_NaiveSubset(subset: NaiveSubset[A], values: Set[Subset]) -> bool:
# def _validContainerOpRelVals_NaiveSubset(subset: NaiveSubset[A], values: Set[NaiveSubset[A]]) -> bool:
  if all([isinstance(v, NaiveSubset) for v in values]):
    return NaiveSubset.same_universes(values) and (len(values) == 0 or NaiveSubset.same_universe(subset, peek(values)))  # type: ignore
  else:
    return _validBinOpRelVals_object(subset, values)

@_validContainerOpArg.instance(delegate=Set_NaiveSubset)
# @_validContainerOpArg.instance(NaiveSubset)
def _validContainerOpArg_NaiveSubset(values: Set[NaiveSubset[A]]) -> bool:
  if all([isinstance(v, NaiveSubset) for v in values]):
    return NaiveSubset.same_universes(values)
  else:
    return _validContainerOpArg_object(values)

@_universe.instance(NaiveSubset)
def _universe_NaiveSubset(p: NaiveSubset[A]) -> set[A]:
  return p.universe

@_subset.instance(NaiveSubset)
def _subset_NaiveSubset(p: NaiveSubset[A]) -> set[A]:
  return p.subset

@_consistent_subset_universe.instance(NaiveSubset)
def _consistent_subset_universe_NaiveSubset(p: NaiveSubset[A]) -> bool:
# def _consistent_subset_universe_NaiveSubset(subset: set[A], universe: set[A]) -> bool:
  return NaiveSubset._consistent_subset_universe(p.subset, p.universe)

@is_empty.instance(NaiveSubset)
def _is_empty_NaiveSubset(value: NaiveSubset[A]) -> bool:
  return value.subset == set()

# #FIXME redundant with default implementation
# @is_nonempty.instance(NaiveSubset)
# def _is_nonempty_NaiveSubset(value: NaiveSubset[A]) -> bool:
#   return not is_empty(value)

@is_universe.instance(NaiveSubset)
def _is_universe_NaiveSubset(value: NaiveSubset[A]) -> bool:
 return value.subset == value.universe

@has_element.instance(NaiveSubset)
def _has_element_NaiveSubset(value: NaiveSubset[A], a: A) -> bool:
 return a in value.subset

# #FIXME redundant with default implementation
# @missing_element.instance(NaiveSubset)
# def _missing_element_NaiveSubset(value: NaiveSubset[A], a: A) -> bool:
#  return not has_element(value, a)

@has_exactly_k_elements.instance(NaiveSubset)
def _has_exactly_k_elements_NaiveSubset(subset: NaiveSubset[A], k: int) -> bool:
  return len(subset) == k

@has_atLeast_k_elements.instance(NaiveSubset)
def _has_atLeast_k_elements_NaiveSubset(subset: NaiveSubset[A], k: int) -> bool:
  return len(subset) >= k

@has_atMost_k_elements.instance(NaiveSubset)
def _has_atMost_k_elements_NaiveSubset(subset: NaiveSubset[A], k: int) -> bool:
  return len(subset) <= k

@is_intersection.instance(NaiveSubset)
def _is_intersection_NaiveSubset(subset: NaiveSubset[A], left: NaiveSubset[A], right: NaiveSubset[A]) -> Bool:
  assert _validBinOpRelVals_NaiveSubset(subset, left, right)
  return eq(NaiveSubset.mk(left.subset.intersection(right.subset), left.universe), subset)

@is_union.instance(NaiveSubset)
def _is_union_NaiveSubset(subset: NaiveSubset[A], left: NaiveSubset[A], right: NaiveSubset[A]) -> Bool:
  assert _validBinOpRelVals_NaiveSubset(subset, left, right)
  return eq(NaiveSubset.mk(left.subset.union(right.subset), left.universe), subset)

@is_difference.instance(NaiveSubset)
def _is_difference_NaiveSubset(subset: NaiveSubset[A], left: NaiveSubset[A], right: NaiveSubset[A]) -> Bool:
  assert _validBinOpRelVals_NaiveSubset(subset, left, right)
  return eq(NaiveSubset.mk(left.subset.difference(right.subset), left.universe), subset)



@dataclass(frozen=True)
class SymbolicVectorSubset(Subset, Generic[A]):
  '''
  Naive z3 implementation of the Subset typeclass: a product type with
    1. a length n tuple of symbolic booleans
    2. a string indicating the human-readable identifier associated with the
       symbolic variables from #1
    3. a Python tuple of unique elements representing
         - the universe of values that the subset is drawn from
         - the ordering over the universe that tells you how to interpret #1
           as a specific subset: subset[i] is True iff universe[i] is in the
           subset.

  NB that the 'frozen' tag only prevents mutation of the fields via this
  object's `__setattr__` and `__delattr__` interface for normal Python reasons.
  '''
  subset: tuple[z3.BoolRef, ...]
  identifier: str
  universe: tuple[A, ...]
  # universe: set[A]
  # universe_order: tuple[A]

  def __hash__(self):
    return hash((frozenset(self.subset), self.identifier, self.universe))

  @staticmethod
  def _consistent_subset_universe(subset: Tuple[z3.BoolRef, ...], universe: Tuple[A, ...]):
    return len(subset) == len(universe)

  # @staticmethod
  # def _consistent_universe_enumeration(universe: Tuple[A, ...], enumeration: _SymbolicEnumeration[A]) -> bool:
  #   return SymbolicVectorSubset.same_universes(enumeration.values)

  # @staticmethod
  # def _consistent_universe_universeOrder(universe: set[A], universe_order: Tuple[A]):
  #   return length(universe) == length(universe_order)

  def unwrap(self) -> Tuple[Tuple[z3.BoolRef, ...], str, Tuple[A, ...]]:
    return (self.subset, self.identifier, self.universe)

  def to_concreteTuple(self, model: z3.ModelRef) -> Tuple[bool, ...]:
    return tuple([ model[b]
                   for b in self.subset
                 ])

  def to_concreteSet(self, model: z3.ModelRef) -> set[A]:
    return { a
             for i, a in enumerate(self.universe)
             if model[self.subset[i]]
           }

  @staticmethod
  def _mk_subset_tuple(num_objects: int, identifier: str) -> Tuple[z3.BoolRef, ...]:
    return tuple([z3.Bool(f"{identifier}_{i}") for i in range(num_objects)])

  @staticmethod
  def mk(identifier: str, universe: Union[Tuple[A, ...], set[A]]) -> 'SymbolicVectorSubset[A]':
    if isinstance(universe, set) or isinstance(universe, frozenset):  # type: ignore
      universe_t = tuple(sorted(universe))  # type: ignore
    else:
      universe_t = universe
    return SymbolicVectorSubset( SymbolicVectorSubset._mk_subset_tuple( len(universe_t)
                                                                      , identifier
                                                                      )
                               , identifier
                               , universe_t
                               )

  @staticmethod
  def mk_from_set(identifier: str, universe: Tuple[A, ...], s: set[A]) -> Tuple['SymbolicVectorSubset[A]', Constraint]:
    if not isinstance(universe, tuple):
      raise Exception(f"universe must be a tuple, got value of type '{type(universe)}': '{universe}'")
    assert s.issubset(set(universe)), f"s={s}\nuniverse={universe}"
    ssv = SymbolicVectorSubset( SymbolicVectorSubset._mk_subset_tuple( len(universe)
                                                                     , identifier
                                                                     )
                              , identifier
                              , universe
                              )
    usv = SymbolicVectorSubset._global_upper_bound_SymbolicVectorSubset(ssv)

    ssConstraints = is_subseteq(ssv, usv)
    eqConstraints = z3.And([ ssv.subset[i] if a in s else z3.Not(ssv.subset[i])
                             for i, a in enumerate(universe)
                           ])
    constraints   = z3.And(ssConstraints, eqConstraints)
    return (ssv, constraints)

  @staticmethod
  def mk_from_tuple(identifier: str, universe: tuple[A, ...], s: tuple[bool, ...]) -> Tuple['SymbolicVectorSubset[A]', Constraint]:
    if not isinstance(universe, tuple):
      raise Exception(f"universe must be a tuple, got value of type '{type(universe)}': '{universe}'")
    if not isinstance(s, tuple):
      raise Exception(f"s must be a tuple, got value of type '{type(universe)}': '{s}")
    ensureSameLength(universe, s)
    ssv = SymbolicVectorSubset( SymbolicVectorSubset._mk_subset_tuple( len(universe)
                                                                     , identifier
                                                                     )
                              , identifier
                              , universe
                              )
    usv = SymbolicVectorSubset._global_upper_bound_SymbolicVectorSubset(ssv)

    ssConstraints = is_subseteq(ssv, usv)
    eqConstraints = z3.And([ ssv.subset[i] == s[i]  # == use where top/bot constants may get tricky?
                             for i, a in enumerate(universe)
                           ])
    constraints   = z3.And(ssConstraints, eqConstraints)
    return (ssv, constraints)

  @staticmethod
  def mk_from_NaiveSubset(identifier: str, universe: tuple[A, ...], ns: NaiveSubset[A]) -> Tuple['SymbolicVectorSubset[A]', Constraint]:
    assert set(universe) == ns.universe
    return SymbolicVectorSubset.mk_from_set(identifier, universe, ns.subset)

  def to_NaiveSubset(self, model: z3.ModelRef) -> NaiveSubset[A]:
    ss = self.to_concreteSet(model)
    u  = set(self.universe)
    return NaiveSubset(ss, u)

  # Obligatory functions (+ helpers) because Subset is an instance of Eq
  @staticmethod
  def same_universe(left: 'SymbolicVectorSubset[A]', right: 'SymbolicVectorSubset[A]') -> bool:
    return left.universe == right.universe

  # @staticmethod
  # def same_universeOrder(left: 'SymbolicVectorSubset[A]', right: 'SymbolicVectorSubset[A]') -> bool:
  #   return left.universe_order == right.universe_order

  @staticmethod
  def same_universes(values: Set['SymbolicVectorSubset[A]']) -> bool:
    values_seq = list(values)
    u0         = values_seq[0].universe
    return all([v.universe == u0 for v in values_seq])

  # @staticmethod
  # def same_universeOrders(values: Set['SymbolicVectorSubset[A]']) -> bool:
  #   values_seq = list(values)
  #   uo0         = values_seq[0].universe_order
  #   return all([v.universe_order == uo0 for v in values_seq])

  @staticmethod
  def _enumerate_atoms_from_universe(universe: tuple[A, ...], identifier: str) -> set[Tuple['SymbolicVectorSubset[A]', Constraint]]:
    assert len(universe) == len(set(universe))
    return set({ SymbolicVectorSubset.mk_from_set( f"{identifier}_atom_{i}"
                                                 , universe
                                                 , {s}
                                                 )
                 for i,s in enumerate(universe)
               })

  # @staticmethod
  # def _enumerate_universe_from_atoms(atoms: Set[Tuple['SymbolicVectorSubset[A]', Constraints]]) -> tuple[A, ...]:
  #   raise NotImplementedError #FIXME revisit if this is important to implement and exactly what's needed by what context - there's more than one plausible use-case/type-signature/implementation

  @staticmethod
  def _global_upper_bound_SymbolicVectorSubset(subset: 'SymbolicVectorSubset[A]') -> 'SymbolicVectorSubset[A]':
    """
    Returns a constant-valued representation of the top element of the powerset.

    Beware subtelties around equality of reference and equality of value:
      - careless use of `==` instead of `eq` may result in subtle bugs.

    For example, if you have a collection of symbolic variables that represent
    a powerset, then the most likely way you've generated this would have e.g.
    a top element that just so happens to be constrained in such a way that it
    is equal in *value* to the top element generated by this method; unless
    you have devised a way to construct your powerset so that *the result of
    this method* is the only element in your collection that is topmost, it will
    not be equal in *reference* to the value returned by this method.
    """
    ident_top = f"{subset.identifier}_top"
    return SymbolicVectorSubset( tuple([ z3.BoolVal(True) # boolean constant!
                                         for b in range(len(subset.universe))
                                       ])
                               , ident_top
                               , subset.universe
                               )

  @staticmethod
  def _global_lower_bound_SymbolicVectorSubset(subset: 'SymbolicVectorSubset[A]') -> 'SymbolicVectorSubset[A]':
    """
    Returns a constant-valued representation of the bottom element of the power-
    set.

    Beware subtelties around equality of reference and equality of value:
      - careless use of `==` instead of `eq` may result in subtle bugs.

    For example, if you have a collection of symbolic variables that represent
    a powerset, then the most likely way you've generated this would have e.g.
    a bottom element that just so happens to be constrained in such a way that it
    is equal in *value* to the bottom element generated by this method; unless
    you have devised a way to construct your powerset so that *the result of
    this method* is the only element in your collection that is bottommost, it
    will not be equal in *reference* to the value returned by this method.
    """
    ident_bot = f"{subset.identifier}_bot"
    return SymbolicVectorSubset( tuple([ z3.BoolVal(False)
                                         for b in range(len(subset.universe))
                                       ])
                               , ident_bot
                               , subset.universe
                               )

  @staticmethod
  def _is_intersection_SymbolicVectorSubset( a: 'SymbolicVectorSubset[A]'
                                           , left: 'SymbolicVectorSubset[A]'
                                           , right: 'SymbolicVectorSubset[A]'
                                           ) -> Constraint:
    assert _validBinOpArgs_SymbolicVectorSubset(left, right)
    assert _validBinOpArgs_SymbolicVectorSubset(left, a)
    return z3.And([ i == z3.And(l,r)  # == use where top/bot constants may get tricky?
                    for l,r,i in zip( left.subset
                                    , right.subset
                                    , a.subset
                                    )
                  ])

  @staticmethod
  def _is_union_SymbolicVectorSubset( a: 'SymbolicVectorSubset[A]'
                                    , left: 'SymbolicVectorSubset[A]'
                                    , right: 'SymbolicVectorSubset[A]'
                                    ) -> Constraint:
    assert _validBinOpArgs_SymbolicVectorSubset(left, right)
    assert _validBinOpArgs_SymbolicVectorSubset(left, a)
    return z3.And([ u == z3.Or(l,r)  # == use where top/bot constants may get tricky?
                    for l,r,u in zip( left.subset
                                    , right.subset
                                    , a.subset
                                    )
                  ])

  @staticmethod
  def _is_difference_SymbolicVectorSubset( a: 'SymbolicVectorSubset[A]'
                                         , left: 'SymbolicVectorSubset[A]'
                                         , right: 'SymbolicVectorSubset[A]'
                                         ) -> Constraint:
    assert _validBinOpArgs_SymbolicVectorSubset(left, right)
    assert _validBinOpArgs_SymbolicVectorSubset(left, a)
    return z3.And([ d == z3.And(l, z3.Not(r))  # == use where top/bot constants may get tricky?
                    for l,r,d in zip( left.subset
                                    , right.subset
                                    , a.subset
                                    )
                  ])


# def _strategy_SymbolicVectorSubset_int(num_elements: int = 3) -> SearchStrategy[SymbolicVectorSubset[int]]:

#   return st.builds( SymbolicVectorSubset
#                   , subset = st.sets( elements = st.integers(min_value = 0, max_value = num_elements)
#                                     , min_size = 0
#                                     , max_size = num_elements + 1
#                                     )
#                   , universe = st.just(set(range(num_elements)))
#                   )

# def _strategy_SymbolicVectorSubset_PS_int(num_elements: int = 3) -> SearchStrategy[Set[SymbolicVectorSubset[int]]]:
#   u = set(range(num_elements))

#   def mk(subset: set[int]) -> SymbolicVectorSubset[int]:
#     return SymbolicVectorSubset(subset, universe = u)

#   ps = more_itertools.powerset(u)

#   return st.just(set(map( mk
#                         , ps
#                         )
#                     )
#                 )

# SV = TypeVar('SV', bound=SymbolicVectorSubset[A])

class _Set_SymbolicVectorSubset_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, Set) \
             and (   len(arg) == 0 \
               or isinstance(peek(arg), SymbolicVectorSubset)
               )
    except Exception:
      return False

class Set_SymbolicVectorSubset(Set[SymbolicVectorSubset], metaclass=_Set_SymbolicVectorSubset_Meta): ...

# Eq

@eq.instance(SymbolicVectorSubset)
def _eq_SymbolicVectorSubset(left: SymbolicVectorSubset[A], right: Subset) -> Constraint:
  if isinstance(right, SymbolicVectorSubset):
    assert _validBinOpArgs_SymbolicVectorSubset(left, right)
    return z3.And([ l == r  # == use where top/bot constants may get tricky?
                    for l, r in zip(left.subset, right.subset)
                  ])
  else:
    return _eq_Subset(left, right)
  # elif isinstance(right, NaiveSubset):
  #   assert _validBinOpArgs_SymbolicVectorSubset_NaiveSubset(left, right)
  #   return z3.And([ l == NaiveSubset.has_element(right, left.universe[i])
  #                   for i, l in enumerate(left.subset)
  #                 ])
  # else:
  #   raise mk_UnknownTypeError(value=right, expectedTypes=[SymbolicVectorSubset[A], NaiveSubset[A]])

@eq1.instance(delegate=Set_SymbolicVectorSubset)
def _eq1_SymbolicVectorSubset(values: Set[SymbolicVectorSubset[A]]) -> Constraint:
  if all([isinstance(v, SymbolicVectorSubset) for v in values]):
    assert _validContainerOpArg_SymbolicVectorSubset(values)
    assert isNonempty(values)
    v0 = peek(values)
    return z3.And([ _eq_SymbolicVectorSubset(v, v0)
                    for v in values
                  ])
  else:
    return _eq1_Subset(values)

# # Preorder

@le.instance(SymbolicVectorSubset)
def _le_SymbolicVectorSubset(left: SymbolicVectorSubset[A], right: SymbolicVectorSubset[A]) -> Constraint:
  assert _validBinOpArgs_SymbolicVectorSubset(left, right)
  return z3.And([ z3.Implies(l, l == r)  # == use where top/bot constants may get tricky?
                  for l,r in zip(left.subset, right.subset)
                ])

@ge.instance(SymbolicVectorSubset)
def _ge_SymbolicVectorSubset(left: SymbolicVectorSubset[A], right: SymbolicVectorSubset[A]) -> Constraint:
  assert _validBinOpArgs_SymbolicVectorSubset(left, right)
  return le(right, left)

@_enumerate_Preorder.instance(SymbolicVectorSubset)
def _enumerate_Preorder_SymbolicVectorSubset(subset: SymbolicVectorSubset[A]) -> _SymbolicEnumeration[SymbolicVectorSubset[A]]:
# def _enumerate_Preorder_SymbolicVectorSubset(subset: SymbolicVectorSubset[A]) -> Set[Tuple[SymbolicVectorSubset[A], Constraint]]:
  '''
  Generates the entire powerset associated with `subset`
  '''
  universe = subset.universe
  subsets  = map( set
                , more_itertools.powerset(set(universe))
                )

  def _mk(arg: Tuple[int, set]) -> Tuple[SymbolicVectorSubset[A], Constraint]:
    i, s = arg
    return SymbolicVectorSubset.mk_from_set( identifier=f"{subset.identifier}_PS_{i}"
                                           , universe=universe
                                           , s=s
                                           )
  subsets_and_constraints = lmap(_mk, enumerate(subsets))
  subsets     = map(fst, subsets_and_constraints)
  constraints = map(snd, subsets_and_constraints)
  return _SymbolicEnumeration.freeze( set(subsets)  # type: ignore
                                    , z3.And(list(constraints))
                                    )

@is_greatest_lower_bound.instance(SymbolicVectorSubset)
def _is_greatest_lower_bound_SymbolicVectorSubset( a: SymbolicVectorSubset[A]
                                                 , left: SymbolicVectorSubset[A]
                                                 , right: SymbolicVectorSubset[A]
                                                 , ps: Optional[Set[SymbolicVectorSubset[A]]]
                                                 ) -> Constraint:
  assert _validBinOpArgs_SymbolicVectorSubset(left, right), f"left={left}\nright={right}"
  assert _validBinOpArgs_SymbolicVectorSubset(left, a), f"left={left}\na={a}"
  if ps is None:
    is_meet_con = SymbolicVectorSubset._is_intersection_SymbolicVectorSubset(a, left, right)
    return is_meet_con
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert _validContainerOpRelVals(left, ps), f"left={left}\nps={ps}"
    assert isNonempty(ps), f"ps={ps}"
    return _is_greatest_lower_bound_object(a, left, right, ps)

@has_greatest_lower_bound.instance(SymbolicVectorSubset)
def _has_greatest_lower_bound_SymbolicVectorSubset( left: SymbolicVectorSubset[A]
                                                  , right: SymbolicVectorSubset[A]
                                                  , ps: Optional[Set[SymbolicVectorSubset[A]]]
                                                  ) -> Constraint:
  assert _validBinOpArgs_SymbolicVectorSubset(left, right), f"left={left}\nright={right}"
  if ps is None:
    return z3.BoolVal(True)  # intersection should be total
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert _validContainerOpRelVals(left, ps), f"left={left}\nps={ps}"
    assert _validContainerOpArg(ps), f"ps={ps}"
    return _has_greatest_lower_bound_object(left, right, ps)

@is_greatest_lower_bound1.instance(SymbolicVectorSubset)
def _is_greatest_lower_bound1_SymbolicVectorSubset( a: SymbolicVectorSubset[A]
                                                  , s: Set[SymbolicVectorSubset[A]]
                                                  , ps: Optional[Set[SymbolicVectorSubset[A]]]
                                                  ) -> Constraint:
  assert _validContainerOpRelVals_SymbolicVectorSubset(a, s), f"a={a}\ns={s}"
  if ps is None:
    def get_subset(ssv: SymbolicVectorSubset[A]) -> tuple[z3.BoolRef, ...]:
      return ssv.subset
    return z3.And([ slice[0] == z3.And(slice[1:])  # == use where top/bot constants may get tricky?
                    for slice in zip( a.subset
                                    , *lmap(get_subset, s)
                                    )
                  ])
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert _validContainerOpRelVals(a, ps), f"a={a}\nps={ps}"
    assert isNonempty(ps), f"ps={ps}"
    assert isNonempty(s), f"s={s}\nps={ps}"
    assert _validContainerOpArg(ps), f"ps={ps}"
    assert _validContainerOpArg(s), f"s={s}"
    assert all([_validContainerOpRelVals(each, ps) for each in s]), f"s={s}\nps={ps}"
    return _is_greatest_lower_bound1_object(a, s, ps)

@has_greatest_lower_bound1.instance(delegate=Set_SymbolicVectorSubset)
def _has_greatest_lower_bound1_SymbolicVectorSubset( s: Set[SymbolicVectorSubset[A]]
                                                   , ps: Optional[Set[SymbolicVectorSubset[A]]]
                                                   ) -> Constraint:
  if ps is None:
    return z3.BoolVal(True)  # meet1 should be total
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert isNonempty(ps), f"ps={ps}"
    assert isNonempty(s), f"s={s}"
    assert _validContainerOpArg(ps), f"ps={ps}"
    assert _validContainerOpArg(s), f"s={s}"
    assert all([_validContainerOpRelVals(each, ps) for each in s]), f"s={s}\nps={ps}"
    return _has_greatest_lower_bound1_object(s, ps)

@is_least_upper_bound.instance(SymbolicVectorSubset)
def _is_least_upper_bound_SymbolicVectorSubset( a: SymbolicVectorSubset[A]
                                              , left: SymbolicVectorSubset[A]
                                              , right: SymbolicVectorSubset[A]
                                              , ps: Optional[Set[SymbolicVectorSubset[A]]]
                                              ) -> Constraint:
  assert _validBinOpArgs_SymbolicVectorSubset(left, right), f"left={left}\nright={right}"
  assert _validBinOpArgs_SymbolicVectorSubset(left, a), f"left={left}\na={a}"
  if ps is None:
    is_join_con = SymbolicVectorSubset._is_union_SymbolicVectorSubset(a, left, right)
    return is_join_con
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert _validContainerOpRelVals(left, ps), f"left={left}\nps={ps}"
    assert isNonempty(ps), f"ps={ps}"
    return _is_least_upper_bound_object(a, left, right, ps)

@has_least_upper_bound.instance(SymbolicVectorSubset)
def _has_least_upper_bound_SymbolicVectorSubset( left: SymbolicVectorSubset[A]
                                               , right: SymbolicVectorSubset[A]
                                               , ps: Optional[Set[SymbolicVectorSubset[A]]]
                                               ) -> Constraint:
  assert _validBinOpArgs_SymbolicVectorSubset(left, right), f"left={left}\nright={right}"
  if ps is None:
    return z3.BoolVal(True)  # union should be total
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert _validContainerOpRelVals(left, ps), f"left={left}\nps={ps}"
    assert _validContainerOpArg(ps), f"ps={ps}"
    return _has_least_upper_bound_object(left, right, ps)

@is_least_upper_bound1.instance(SymbolicVectorSubset)
def _is_least_upper_bound1_SymbolicVectorSubset( a: SymbolicVectorSubset[A]
                                               , s: Set[SymbolicVectorSubset[A]]
                                               , ps: Optional[Set[SymbolicVectorSubset[A]]]
                                               ) -> Constraint:
  assert _validContainerOpRelVals_SymbolicVectorSubset(a, s), f"a={a}\ns={s}"
  if ps is None:
    def get_subset(ssv: SymbolicVectorSubset[A]) -> tuple[z3.BoolRef, ...]:
      return ssv.subset
    return z3.And([ slice[0] == z3.Or(slice[1:])  # == use where top/bot constants may get tricky?
                    for slice in zip( a.subset
                                    , *lmap(get_subset, s)
                                    )
                  ])
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert _validContainerOpRelVals(a, ps), f"a={a}\nps={ps}"
    assert isNonempty(ps), f"ps={ps}"
    assert isNonempty(s), f"s={s}\nps={ps}"
    assert _validContainerOpArg(ps), f"ps={ps}"
    assert _validContainerOpArg(s), f"s={s}"
    assert all([_validContainerOpRelVals(each, ps) for each in s]), f"s={s}\nps={ps}"
    return _is_least_upper_bound1_object(a, s, ps)

@has_least_upper_bound1.instance(delegate=Set_SymbolicVectorSubset)
def _has_least_upper_bound1_SymbolicVectorSubset( s: Set[SymbolicVectorSubset[A]]
                                                , ps: Optional[Set[SymbolicVectorSubset[A]]]
                                                ) -> Constraint:
  if ps is None:
    return z3.BoolVal(True)  # join1 should be total
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert isNonempty(ps), f"ps={ps}"
    assert isNonempty(s), f"s={s}"
    assert _validContainerOpArg(ps), f"ps={ps}"
    assert _validContainerOpArg(s), f"s={s}"
    assert all([_validContainerOpRelVals(each, ps) for each in s]), f"s={s}\nps={ps}"
    return _has_least_upper_bound1_object(s, ps)

@covers.instance(SymbolicVectorSubset)
def _covers_SymbolicVectorSubset(c: SymbolicVectorSubset[A], a: SymbolicVectorSubset[A], ps: Optional[Set[SymbolicVectorSubset[A]]]) -> Bool:
  assert _validBinOpArgs(c, a), f"c={c}, a={a}"
  if ps is None:
    atoms_and_constraints: Set[Tuple[SymbolicVectorSubset[A], Constraint]] = SymbolicVectorSubset._enumerate_atoms_from_universe(c.universe, f"{c.identifier}|{a.identifier}.")
    atoms, atoms_constraints = lmap(fst, atoms_and_constraints), lmap(snd, atoms_and_constraints)
    cover_con = z3.And( distinct(c, a)
                      , z3.Or([ SymbolicVectorSubset._is_difference_SymbolicVectorSubset(a, c, atom)
                                for atom in atoms
                              ])
                      )
    return z3.And( [cover_con] + atoms_constraints )
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    assert _validContainerOpRelVals(c, ps), f"c={c}\nps={ps}"
    assert isNonempty(ps), f"ps={ps}"
    return _covers_object(c, a, ps)

# LowerBounded

@global_lower_bound.instance(SymbolicVectorSubset)
def _global_lower_bound_SymbolicVectorSubset(p: SymbolicVectorSubset[A], ps: Optional[Set[SymbolicVectorSubset[A]]]) -> SymbolicVectorSubset[A]:
  if ps is None:
    return SymbolicVectorSubset._global_lower_bound_SymbolicVectorSubset(p)
  else:
    # TODO - in principle, if you were willing to change the return type, you could return a
    # fresh symbolic vector + a constraint defining that the the fresh vector is the global
    # lower bound of everything in ps.
    # Even if you're not willing to change the return type on *this* specific function/name,
    # a separate function that does this would be useful.
    raise NotImplementedError(f"Not implementable. Use relational forms instead, if possible.")

@is_global_lower_bound.instance(SymbolicVectorSubset)
def _is_global_lower_bound_SymbolicVectorSubset(p: SymbolicVectorSubset[A], ps: Optional[Set[SymbolicVectorSubset[A]]]) -> Constraint:
  if ps is None:
    bot_constant = SymbolicVectorSubset._global_lower_bound_SymbolicVectorSubset(p)  # FIXME update call if necessary whenever the dust settles on a functional interface
    return eq(bot_constant, p)
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    return _is_global_lower_bound_object(p, ps)

@is_atom.instance(SymbolicVectorSubset)
def _is_atom_SymbolicVectorSubset(p: SymbolicVectorSubset[A], ps: Optional[Set[SymbolicVectorSubset[A]]]) -> Constraint:
  if ps is None:
    bot_constant = SymbolicVectorSubset._global_lower_bound_SymbolicVectorSubset(p)
    return covers(p, bot_constant, None)
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    return _is_atom_object(p, ps)

# UpperBounded

@global_upper_bound.instance(SymbolicVectorSubset)
def _global_upper_bound_SymbolicVectorSubset(p: SymbolicVectorSubset[A], ps: Optional[Set[SymbolicVectorSubset[A]]]) -> SymbolicVectorSubset[A]:
  if ps is None:
    return SymbolicVectorSubset._global_upper_bound_SymbolicVectorSubset(p)
  else:
    # TODO - in principle, if you were willing to change the return type, you could return a
    # fresh symbolic vector + a constraint defining that the the fresh vector is the global
    # upper bound of everything in ps.
    # Even if you're not willing to change the return type on *this* specific function/name,
    # a separate function that does this would be useful.
    raise NotImplementedError(f"Not implementable. Use relational forms instead, if possible.")

@is_global_upper_bound.instance(SymbolicVectorSubset)
def _is_global_upper_bound_SymbolicVectorSubset(p: SymbolicVectorSubset[A], ps: Optional[Set[SymbolicVectorSubset[A]]]) -> Constraint:
  if ps is None:
    top_constant = SymbolicVectorSubset._global_upper_bound_SymbolicVectorSubset(p)  # FIXME update call if necessary whenever the dust settles on a functional interface
    return eq(top_constant, p)
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    return _is_global_upper_bound_object(p, ps)

# ComplementedLattice

@complementary.instance(SymbolicVectorSubset)
def _complementary_SymbolicVectorSubset( left: SymbolicVectorSubset[A]
                                       , right: SymbolicVectorSubset[A]
                                       , ps: Optional[Set[SymbolicVectorSubset[A]]]
                                       ) -> Constraint:
  assert _validBinOpArgs_SymbolicVectorSubset(left, right), f"left={left}\nright={right}"
  if ps is None:
    top = SymbolicVectorSubset._global_upper_bound_SymbolicVectorSubset(left)
    bot = SymbolicVectorSubset._global_lower_bound_SymbolicVectorSubset(left)
    return z3.And( is_meet(bot, left, right, ps)
                 , is_join(top, left, right, ps)
                 )
    # return And( SymbolicVectorSubset._is_difference_SymbolicVectorSubset(right, top, left)
    #           , SymbolicVectorSubset._is_difference_SymbolicVectorSubset(left , top, right)
    #           )
  else:
    # TODO - revise/supplement existing slew of _valid<...> functions to accomodate `ps`
    return _complementary_object(left, right, ps)


# Subset

@_validBinOpRelVals.instance(SymbolicVectorSubset)
def _validBinOpRelVals_SymbolicVectorSubset( subset: SymbolicVectorSubset[A]
                                           , left: SymbolicVectorSubset[A]
                                           , right: SymbolicVectorSubset[A]
                                           ) -> bool:
  argsValid      = SymbolicVectorSubset._consistent_subset_universe(subset.subset, subset.universe) and \
                   SymbolicVectorSubset._consistent_subset_universe(left.subset  , left.universe) and \
                   SymbolicVectorSubset._consistent_subset_universe(right.subset , right.universe)
  universesValid = SymbolicVectorSubset.same_universe(left, right) and SymbolicVectorSubset.same_universe(subset, left)
  if not argsValid:
    if not _consistent_subset_universe(subset):
      raise Exception(f"Inconsistent subset vs. universe: {subset}")
    if not _consistent_subset_universe(left):
      raise Exception(f"Inconsistent subset vs. universe: {left}")
    if not _consistent_subset_universe(right):
      raise Exception(f"Inconsistent subset vs. universe: {right}")
  if not universesValid:
    if not (_universe(subset) == _universe(left)):
      raise Exception(f"Universes not equal: {_universe(left)} != {_universe(subset)}\nleft={left}\nright={subset}")
    if not (_universe(right) == _universe(left)):
      raise Exception(f"Universes not equal: {_universe(right)} != {_universe(right)}\nleft={left}\nright={right}")
  return argsValid and universesValid

@_validBinOpArgs.instance(SymbolicVectorSubset)
def _validBinOpArgs_SymbolicVectorSubset(left: SymbolicVectorSubset[A], right: SymbolicVectorSubset[A]) -> bool:
  argsValid      = SymbolicVectorSubset._consistent_subset_universe(left.subset , left.universe) and \
                   SymbolicVectorSubset._consistent_subset_universe(right.subset, right.universe)
  universesValid = _universe(left) == _universe(right)
  if not argsValid:
    if not SymbolicVectorSubset._consistent_subset_universe(left.subset , left.universe):
      raise Exception(f"Inconsistent subset vs. universe: {left}")
    if not SymbolicVectorSubset._consistent_subset_universe(right.subset , right.universe):
      raise Exception(f"Inconsistent subset vs. universe: {right}")
  if not universesValid:
    raise Exception(f"Universes not equal: {_universe(left)} != {_universe(right)}\nleft={left}\nright={right}")
  return universesValid and argsValid

@_validContainerOpRelVals.instance(SymbolicVectorSubset)
def _validContainerOpRelVals_SymbolicVectorSubset(subset: SymbolicVectorSubset[A], values: Set[SymbolicVectorSubset[A]]) -> bool:
  argsValid      = SymbolicVectorSubset._consistent_subset_universe(subset.subset, subset.universe) and \
                   all([ SymbolicVectorSubset._consistent_subset_universe(v.subset, v.universe)
                         for v in values
                       ])
  universesValid = SymbolicVectorSubset.same_universes(values) and \
                   (len(values) == 0 or SymbolicVectorSubset.same_universe(subset, peek(values)))  # type: ignore
  return argsValid and universesValid

@_validContainerOpArg.instance(delegate=Set_SymbolicVectorSubset)
def _validContainerOpArg_SymbolicVectorSubset(values: Set[SymbolicVectorSubset[A]]) -> bool:
  return SymbolicVectorSubset.same_universes(values) and \
         all([ SymbolicVectorSubset._consistent_subset_universe(v.subset, v.universe)
               for v in values
             ])

@_universe.instance(SymbolicVectorSubset)
def _universe_SymbolicVectorSubset(p: SymbolicVectorSubset[A]) -> set[A]:
  return set(p.universe)

@_subset.instance(SymbolicVectorSubset)
def _subset_SymbolicVectorSubset(p: SymbolicVectorSubset[A]) -> tuple[z3.BoolRef, ...]:
  return p.subset

@_consistent_subset_universe.instance(SymbolicVectorSubset)
def _consistent_subset_universe_SymbolicVectorSubset(p: SymbolicVectorSubset[A]) -> bool:
  return SymbolicVectorSubset._consistent_subset_universe(p.subset, p.universe)

@has_element.instance(SymbolicVectorSubset)
def _has_element_SymbolicVectorSubset(value: SymbolicVectorSubset[A], a: A) -> Constraint:
  assert a in value.universe
  return value.subset[value.universe.index(a)]

@has_exactly_k_elements.instance(SymbolicVectorSubset)
def _has_exactly_k_elements_SymbolicVectorSubset(subset: SymbolicVectorSubset[A], k: int) -> Constraint:
  assert k <= len(subset.subset)
  return z3.And( z3.AtLeast(*subset.subset, k)
               , z3.AtMost(*subset.subset, k)
               )

@has_atLeast_k_elements.instance(SymbolicVectorSubset)
def _has_atLeast_k_elements_SymbolicVectorSubset(subset: SymbolicVectorSubset[A], k: int) -> Constraint:
  assert k <= len(subset.subset)
  return z3.AtLeast(*subset.subset, k)

@has_atMost_k_elements.instance(SymbolicVectorSubset)
def _has_atMost_k_elements_SymbolicVectorSubset(subset: SymbolicVectorSubset[A], k: int) -> Constraint:
  assert k <= len(subset.subset)
  return z3.AtMost(*subset.subset, k)

@is_intersection.instance(SymbolicVectorSubset)
def _is_intersection_SymbolicVectorSubset( subset: SymbolicVectorSubset[A]
                                         , left: SymbolicVectorSubset[A]
                                         , right: SymbolicVectorSubset[A]
                                         ) -> Bool:
  assert _validBinOpRelVals_SymbolicVectorSubset(subset, left, right)
  return SymbolicVectorSubset._is_intersection_SymbolicVectorSubset(subset, left, right)

@is_union.instance(SymbolicVectorSubset)
def _is_union_SymbolicVectorSubset( subset: SymbolicVectorSubset[A]
                                  , left: SymbolicVectorSubset[A]
                                  , right: SymbolicVectorSubset[A]
                                  ) -> Bool:
  assert _validBinOpRelVals_SymbolicVectorSubset(subset, left, right)
  return SymbolicVectorSubset._is_union_SymbolicVectorSubset(subset, left, right)

@is_difference.instance(SymbolicVectorSubset)
def _is_difference_SymbolicVectorSubset( subset: SymbolicVectorSubset[A]
                                       , left: SymbolicVectorSubset[A]
                                       , right: SymbolicVectorSubset[A]
                                       ) -> Bool:
  assert _validBinOpRelVals_SymbolicVectorSubset(subset, left, right)
  return SymbolicVectorSubset._is_difference_SymbolicVectorSubset(subset, left, right)

# def _same_universe_SymbolicVectorSubset_NaiveSubset(left: SymbolicVectorSubset[A], right: NaiveSubset[A]) -> bool:
#   return set(left.universe) == right.universe

# def _validBinOpArgs_SymbolicVectorSubset_NaiveSubset(left: SymbolicVectorSubset[A], right: NaiveSubset[A]) -> bool:
#   return _same_universe_SymbolicVectorSubset_NaiveSubset(left, right) and \
#          SymbolicVectorSubset._consistent_subset_universe(left.subset , left.universe) and \
#          NaiveSubset._consistent_subset_universe(right.subset, right.universe)


# TODO - finish implementation
@dataclass(frozen=True)
class SymbolicArraySubset(Subset, Generic[A]):
  '''
  z3-backed symbolic subset implementation using the z3 idiom of representing
  subsets using the theory of arrays.
  '''
  subset: z3Map
  identifier: str
  universe: tuple[A, ...]
  _universe_sort: SymbolicSort[A]
  _codomain_sort: SymbolicSort[bool]

  @staticmethod
  def _consistent_universe_sorts_and_subset( universe: Tuple[A, ...]
                                           , universe_sort: SymbolicSort[A]
                                           , codomain_sort: SymbolicSort[bool]
                                           , subset: z3Map
                                           ) -> bool:
    ...

  @staticmethod
  def same_universe(left: 'SymbolicArraySubset[A]', right: 'SymbolicArraySubset[A]') -> bool:
    return left.universe == right.universe

  @staticmethod
  def same_universes(values: Set['SymbolicArraySubset[A]']) -> bool:
    values_seq = list(values)
    u0         = values_seq[0].universe
    return all([v.universe == u0 for v in values_seq])

  def unwrap(self) -> Tuple[z3Map, str, Tuple[A, ...], SymbolicSort[A], SymbolicSort[bool]]:
    return (self.subset, self.identifier, self.universe, self._universe_sort, self._codomain_sort)

  def to_concreteSet(self, model: z3.ModelRef) -> FrozenSet[A]:
    ...

  def to_NaiveSubset(self, model: z3.ModelRef) -> NaiveSubset[A]:
    ...

  @staticmethod
  def mk( identifier: str
        , universe: Union[Tuple[A, ...], Set[A]]
        , universe_sort: Optional[SymbolicSort[A]] = None
        , codomain_sort: Optional[SymbolicSort[bool]] = None
        ) -> 'SymbolicArraySubset[A]':
    ...


  @staticmethod
  def mk_from_set( identifier: str
                 , universe: Union[Tuple[A, ...], Set[A]]
                 , s: Set[A]
                 , universe_sort: Optional[SymbolicSort[A]] = None
                 , codomain_sort: Optional[SymbolicSort[bool]] = None
                 ) -> Tuple['SymbolicArraySubset[A]', Constraint]:
    ...

  @staticmethod
  def mk_from_tuple( identifier: str
                   , universe: Union[Tuple[A, ...], Set[A]]
                   , s: Tuple[bool, ...]
                   , universe_sort: Optional[SymbolicSort[A]] = None
                   , codomain_sort: Optional[SymbolicSort[bool]] = None
                   ) -> Tuple['SymbolicArraySubset[A]', Constraint]:
    ...


  @staticmethod
  def mk_from_NaiveSubset( identifier: str
                         , universe: Union[Tuple[A, ...], Set[A]]
                         , s: Tuple[bool, ...]
                         , universe_sort: Optional[SymbolicSort[A]] = None
                         , codomain_sort: Optional[SymbolicSort[bool]] = None
                         ) -> Tuple['SymbolicArraySubset[A]', Constraint]:
    ...

  @staticmethod
  def _enumerate_atoms_from_universe(universe: tuple[A, ...], identifier: str) -> set[Tuple['SymbolicArraySubset[A]', Constraint]]:
    ensureSameLength(universe, set(universe))  # type: ignore
    return set({ SymbolicArraySubset.mk_from_set( f"{identifier}_atom_{i}"
                                                , universe
                                                , {s}
                                                )
                 for i,s in enumerate(universe)
               })

  @staticmethod
  def _global_upper_bound_SymbolicArraySubset(subset: 'SymbolicArraySubset[A]') -> 'SymbolicArraySubset[A]':
    ...


  @staticmethod
  def _global_lower_bound_SymbolicArraySubset(subset: 'SymbolicArraySubset[A]') -> 'SymbolicArraySubset[A]':
    ...


  @staticmethod
  def _is_intersection_SymbolicArraySubset( a: 'SymbolicArraySubset[A]'
                                          , left: 'SymbolicArraySubset[A]'
                                          , right: 'SymbolicArraySubset[A]'
                                          ) -> Constraint:
    assert _validBinOpArgs(left, right)
    assert _validBinOpArgs(left, a)
    ...

  @staticmethod
  def _is_union_SymbolicArraySubset( a: 'SymbolicArraySubset[A]'
                                   , left: 'SymbolicArraySubset[A]'
                                   , right: 'SymbolicArraySubset[A]'
                                   ) -> Constraint:
    assert _validBinOpArgs(left, right)
    assert _validBinOpArgs(left, a)
    ...

  @staticmethod
  def _is_difference_SymbolicArraySubset( a: 'SymbolicArraySubset[A]'
                                        , left: 'SymbolicArraySubset[A]'
                                        , right: 'SymbolicArraySubset[A]'
                                        ) -> Constraint:
    assert _validBinOpArgs(left, right)
    assert _validBinOpArgs(left, a)
    ...


class _Set_SymbolicArraySubset_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, Set) \
             and (   len(arg) == 0 \
               or isinstance(peek(arg), SymbolicArraySubset)
               )
    except Exception:
      return False

class Set_SymbolicArraySubset(Set[SymbolicArraySubset], metaclass=_Set_SymbolicArraySubset_Meta): ...

# TODO - typeclass implementations...


# Eq


# Preorder


# LowerBounbed


# UpperBounded


# PartialOrder


# ComplementedLattice


# Subset




# CVC5 subsets?
