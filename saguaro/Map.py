'''
Module defining an interface (and some instances) for partial binary relations
and partial functions to and from finite sets.
'''

from dataclasses import dataclass
from typing import TypeVar, Generic, Optional, Union, \
                   Sized, Collection, \
                   Set, FrozenSet, Tuple, List, \
                   Dict, Mapping, Callable
from classes import AssociatedType, Supports, typeclass

# import bidict as bd
# from bidict import bidict

from pyrsistent import m, pmap

from funcy import lmap, lfilter, group_by
from itertools import product
# import more_itertools

# from random import randint, sample#, shuffle, choice, choices


import z3

import saguaro.utilities as SU
import saguaro.Eq        as SE
import saguaro._Boolean  as SB
import saguaro.Order     as SO
import saguaro.Subset    as SS

from saguaro.utilities import foldl, peek, fst, snd, _eq_as_function
from saguaro.utilities import ensureSameLength
from saguaro.utilities import A, B
from saguaro.utilities import z3Sort, z3Constant, z3Map, \
                              Sort, ConcreteSort, SymbolicSort, \
                              mk_map_from_SymbolicArray#, mk_EnumRef
from saguaro.utilities import Pair, PairSeq, Graph
from saguaro.utilities import mk_map_from_function_over, mk_function_from_map, \
                              mk_graph, mk_graph1, all_partial_maps, \
                              override, prunion, \
                              is_defined, is_defined_at, \
                              has_explicit_nullMaps, drop_explicit_nullMaps, \
                              pad_with_explicit_nullMaps, \
                              dod, common_dod, eq_dod, \
                              eq_defined_maps, equalizer, \
                              fixmaps, mumaps, fixpoints, mupoints#, compose, tie, is_undefined
from saguaro._Boolean import Bool, Constraint, Not#, Not1, And, And1, Or, Or1, Implies, Iff, Iff1
from saguaro.Eq import eq, eq1, neq, neq1, distinct
from saguaro.Order import le, ge, lt, gt, lt1, gt1, \
                          comparable, is_between, is_in_interval, \
                          is_maximal, is_minimal, \
                          is_upper_bound, is_lower_bound, \
                          is_least_upper_bound, is_least_upper_bound1, \
                          is_greatest_lower_bound, is_greatest_lower_bound1, \
                          is_join, is_join1, is_meet, is_meet1, \
                          has_least_upper_bound, has_least_upper_bound1, \
                          has_greatest_lower_bound, has_greatest_lower_bound1, \
                          has_join, has_join1, has_meet, has_meet1, \
                          is_global_lower_bound, is_global_upper_bound, \
                          complementary
# from saguaro.Order import Preorder, PartialOrder, LowerBounded, UpperBounded
# from saguaro.Order import MeetSemilattice, JoinSemilattice
# from saguaro.Order import ComplementedLattice, DistributiveLattice,
# from saguaro.Order import BooleanLattice
# from saguaro.Order import OverridingNearlattice, BooleanNearlattice
from saguaro.Order import BooleanOverridingNearlattice
from saguaro.Subset import Subset, NaiveSubset, SymbolicVectorSubset
from saguaro.Subset import is_subseteq

from hypothesis import strategies as st
from hypothesis.strategies import SearchStrategy, sampled_from


# TODO - determine reasonable type to inherit from / typeclasses to implement
# class Relation:
#   """Associated type for a typeclass representing partial binary relations to/from finite sets"""

# R = TypeVar("R", bound=Supports[Relation])

# @dataclass(frozen=True)
# class NaiveSubsetRelation(NaiveSubset, Relation, Generic[A, B]):
#   domain    : ConcreteSort[A]
#   codomain  : ConcreteSort[B]


class PartialFunction(BooleanOverridingNearlattice, Generic[A, B]):
# class PartialFunction(Generic[A, B], BooleanOverridingNearlattice):
# class PartialFunction(Generic[A, B], OverridingNearlattice, BooleanNearlattice):
  """Associated type for a typeclass representing partial functions to/from finite sets"""

PF = TypeVar("PF", bound=Supports[PartialFunction])

class _Set_PartialFunction_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, Set) \
             and (   len(arg) == 0 \
               or isinstance(peek(arg), PartialFunction)
               )
    except Exception:
      return False

class Set_PartialFunction(Set[PartialFunction], metaclass=_Set_PartialFunction_Meta): ...

class _FrozenSet_PartialFunction_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, FrozenSet) \
             and (   len(arg) == 0 \
               or isinstance(peek(arg), PartialFunction)
               )
    except Exception:
      return False

class FrozenSet_PartialFunction(FrozenSet[PartialFunction], metaclass=_FrozenSet_PartialFunction_Meta): ...

@typeclass(PartialFunction)
def domain(f: PartialFunction) -> FrozenSet[A]: ...

@typeclass(PartialFunction)
def codomain(f: PartialFunction) -> FrozenSet[Optional[B]]: ...

@typeclass(PartialFunction)
def is_in_dom(f: PartialFunction, a: A) -> Bool: ...

@typeclass(PartialFunction)
def is_in_dod(f: PartialFunction, a: A) -> Bool: ...

@typeclass(PartialFunction)
def is_undefined(f: PartialFunction, a: A) -> Bool: ...

@typeclass(PartialFunction)
def is_in_cod(f: PartialFunction, b: Optional[B]) -> Bool: ...

@typeclass(PartialFunction)
def is_in_image(f: PartialFunction, b: Optional[B]) -> Bool: ...

@typeclass(PartialFunction)
def is_fixpoint(f: PartialFunction, a: A) -> Bool: ...

@typeclass(PartialFunction)
def is_mupoint(f: PartialFunction, a: A) -> Bool: ...

@typeclass(PartialFunction)
def is_in_graph(f: PartialFunction, mapping: Tuple[A, Optional[B]]) -> Bool: ...

@typeclass(PartialFunction)
def is_fixmap(f: PartialFunction, mapping: Tuple[A, Optional[B]]) -> Bool: ...

@typeclass(PartialFunction)
def is_mumap(f: PartialFunction, mapping: Tuple[A, Optional[B]]) -> Bool: ...

@typeclass(PartialFunction)
def are_in_same_fiber(f: PartialFunction, a: A, b: A) -> Bool: ...

@typeclass(PartialFunction)
def is_composition_of(h: PartialFunction, g: PartialFunction, f: PartialFunction) -> Bool: ...

@typeclass(PartialFunction)
def is_override_of(o: PartialFunction, l: PartialFunction, r: PartialFunction) -> Bool: ...

@typeclass(PartialFunction)
def is_prunion_of(p: PartialFunction, l: PartialFunction, r: PartialFunction) -> Bool: ...

@typeclass(PartialFunction)
def is_tie_of(t: PartialFunction, l: PartialFunction, r: PartialFunction) -> Bool: ...

@typeclass(PartialFunction)
def is_subtraction_of(s: PartialFunction, l: PartialFunction, r: PartialFunction) -> Bool: ...



@dataclass(frozen=True)
class NaiveFunction(PartialFunction, Generic[A, B]):
  identifier: str
  domain    : ConcreteSort[A]
  codomain  : ConcreteSort[B]
  map       : Mapping[A, Optional[B]]
  pairs     : PairSeq
  graph     : Graph
  function  : Callable[[A], Optional[B]]

  @staticmethod
  def _consistent_map_sorts(domain: ConcreteSort[A], codomain: ConcreteSort[B], map: Mapping[A, Optional[B]]) -> bool:
    not_in_domain_sort   = lfilter( lambda k: k not in domain.values
                                  , map.keys()
                                  )
    not_in_codomain_sort = lfilter( lambda k: k not in codomain.values
                                  , map.values()
                                  )
    assert len(not_in_domain_sort)   == 0, f"Keys of map missing from domain sort: '{not_in_domain_sort}'\ndomain={domain}\ncodomain={codomain}\nmap={map}"
    assert len(not_in_codomain_sort) == 0, f"Values of map missing from codomain sort: '{not_in_codomain_sort}'\ndomain={domain}\ncodomain={codomain}\nmap={map}"
    return True

  @staticmethod
  def _same_domain_codomain_values(f: 'NaiveFunction[A, B]', g: 'NaiveFunction[A, B]') -> bool:
    same_domains = f.domain.values == g.domain.values
    same_codomains = f.codomain.values == g.codomain.values
    return same_domains and same_codomains

  @staticmethod
  def mk_from_map( identifier: str
                 , dom: ConcreteSort[A]
                 , cod: ConcreteSort[B]
                 , map: Mapping[A, Optional[B]]
                 ) -> 'NaiveFunction[A,B]':
    assert NaiveFunction._consistent_map_sorts(dom, cod, map)
    return NaiveFunction(identifier, dom, cod, map, mk_graph1(map), mk_graph(map), mk_function_from_map(map))

  @staticmethod
  def mk_from_pairs( identifier: str
                   , dom: ConcreteSort[A]
                   , cod: ConcreteSort[B]
                   , pairs: PairSeq
                   ) -> 'NaiveFunction[A,B]':
    map = pmap(pairs)
    assert NaiveFunction._consistent_map_sorts(dom, cod, map)
    return NaiveFunction(identifier, dom, cod, map, pairs, frozenset(pairs), mk_function_from_map(map))

  @staticmethod
  def mk_from_graph( identifier: str
                   , dom: ConcreteSort[A]
                   , cod: ConcreteSort[B]
                   , graph: FrozenSet[Pair]
                   ) -> 'NaiveFunction[A,B]':
    map = pmap(graph)
    assert NaiveFunction._consistent_map_sorts(dom, cod, map)
    return NaiveFunction(identifier, dom, cod, map, tuple(graph), graph, mk_function_from_map(map))

  @staticmethod
  def mk_from_function( identifier: str
                      , dom: ConcreteSort[A]
                      , cod: ConcreteSort[B]
                      , function: Callable[[A], Optional[B]]
                      , domain_of_definition: Optional[FrozenSet[A]] = None
                      ) -> 'NaiveFunction[A,B]':
    if domain_of_definition is None:
      map = mk_map_from_function_over(function, dom.values)  # type: ignore
    else:
      assert all([each in dom.values for each in domain_of_definition]), f"domain_of_definition={domain_of_definition}\ndom={dom}"
      map = mk_map_from_function_over(function, domain_of_definition)  # type: ignore
    assert all([each in cod.values for each in map.values()]), f"cod={cod}\nmap={map}"
    return NaiveFunction.mk_from_map(identifier, dom, cod, map)

  @staticmethod
  def _apply_NaiveFunction(f: 'NaiveFunction[A, B]', a: A) -> Optional[B]:
    assert a in f.domain.values, f"{a=}\n{f.domain.values=}\n{f=}"
    return f.map[a]

  @staticmethod
  def _restrictTo_NaiveFunction(f: 'NaiveFunction[A, B]', As: FrozenSet[A], identifier: Optional[str] = None) -> 'NaiveFunction[A, B]':
    """
    `f|_As`

    Return a new version of `f` with domain (of definition) restricted to `As`.

    (The `domain` field is left untouched.)
    """
    if identifier is None:
      identifier = f"{f.identifier}_restriction"

    missing_from_dom = [a for a in As if a not in f.domain.values]
    assert len(missing_from_dom) == 0, f"{missing_from_dom=}"

    old_map = f.map
    new_dod = frozenset(dod(old_map, eq=None, nullValue=None)).intersection(As)
    new_map = pmap({ k:old_map[k] for k in old_map if k in new_dod })
    return NaiveFunction.mk_from_map(identifier, f.domain, f.codomain, new_map)

  @staticmethod
  def _subtract_NaiveFunction(f: 'NaiveFunction[A, B]', g: 'NaiveFunction[A, B]', identifier: Optional[str] = None) -> 'NaiveFunction[A, B]':
    """
    `f - g` = f restricted to the complement of g's domain of definition.
    """
    assert NaiveFunction._same_domain_codomain_values(f,g), f"{f=}\n{g=}"
    if identifier is None:
      identifier = f"{f.identifier}_sub_{g.identifier}"

    g_dod = frozenset(dod(g.map, eq=None, nullValue=None))
    f_dod = frozenset(dod(f.map, eq=None, nullValue=None))
    new_f_dod = f_dod.difference(g_dod)
    return NaiveFunction._restrictTo_NaiveFunction(f, new_f_dod, identifier)

  @staticmethod
  def _override_NaiveFunction(f: 'NaiveFunction[A, B]', g: 'NaiveFunction[A, B]', identifier: Optional[str] = None) -> 'NaiveFunction[A, B]':
    """
    Override. (Synonym for left priority union.)

    AKA `clobber`, `priority union`, preferential union.
    See:
    - Karttunnen ????, #fixme
    - Stokes (2021) - Override and restricted union for partial functions
    - Cirulis (2011) - ???
    - Jackson & Stokes (2011) - Modal restriction semigroups: towards an algebra of functions
    """
    assert NaiveFunction._same_domain_codomain_values(f,g), f"{f=}\n{g=}"
    if identifier is None:
      identifier = f"{f.identifier}_ovr_{g.identifier}"

    new_map = override(f.map, g.map, eq=None, nullValue=None)
    return NaiveFunction.mk_from_map(identifier, f.domain, f.codomain, new_map)

  @staticmethod
  def _prunion_NaiveFunction(g: 'NaiveFunction[A, B]', f: 'NaiveFunction[A, B]', identifier: Optional[str] = None) -> 'NaiveFunction[A, B]':
    """
    (Right) priority union.

    AKA `clobber`, `override`, preferential union.
    See:
    - Karttunnen ????, #fixme
    - Stokes (2021) - Override and restricted union for partial functions
    - Cirulis (2011) - ???
    - Jackson & Stokes (2011) - Modal restriction semigroups: towards an algebra of functions
    """
    if identifier is None:
      identifier = f"{g.identifier}_prun_{f.identifier}"

    return NaiveFunction._override_NaiveFunction(g, f, identifier)

  @staticmethod
  def _intersection_NaiveFunction(f: 'NaiveFunction[A, B]', g: 'NaiveFunction[A, B]', identifier: Optional[str] = None) -> 'NaiveFunction[A, B]':
    assert NaiveFunction._same_domain_codomain_values(f,g), f"{f=}\n{g=}"
    if identifier is None:
      identifier = f"{f.identifier}_cap_{g.identifier}"

    return NaiveFunction._restrictTo_NaiveFunction(f, equalizer(f.map, g.map, eq=None, nullValue=None), identifier)

  # @staticmethod
  # def _restrictedUnion_NaiveFunction(f: 'NaiveFunction[A, B]', g: 'NaiveFunction[A, B]', identifier: Optional[str] = None) -> 'NaiveFunction[A, B]':
  #   """
  #   `f 𝛄 g` = the union of
  #     1. g - f
  #     2. f - g
  #     3. f \cap g

  #   In words, f \gamma g contains all mappings of f and g except those where f and
  #   g conflict.
  #   """
  #   assert NaiveFunction._same_domain_codomain_values(f,g), f"{f=}\n{g=}"
  #   if identifier is None:
  #     identifier = f"{f.identifier}_ru_{g.identifier}"

  #   g_minus_f = NaiveFunction._subtract_NaiveFunction(f, g)
  #   f_minus_g = NaiveFunction._subtract_NaiveFunction(g, f)
  #   f_cap_g   = NaiveFunction._intersection_NaiveFunction(f, g)
  #   new_map   = override(g_minus_f.map, override(f_minus_g.map, f_cap_g.map, eq=None, nullValue=None), eq=None, nullValue=None)
  #   return NaiveFunction.mk_from_map(identifier, f.domain, f.codomain, new_map)

  # @staticmethod
  # def _tie_NaiveFunction(f: 'NaiveFunction[A, B]', g: 'NaiveFunction[A, B]', identifier: Optional[str] = None) -> 'NaiveFunction[A, B]':
  #   """
  #   `f ⧓ g`
  #   Return the identity map restricted to where f and g 'disagree'.
  #   """
  #   assert NaiveFunction._same_domain_codomain_values(f,g), f"{f=}\n{g=}"
  #   if identifier is None:
  #     identifier = f"{f.identifier}_tie_{g.identifier}"

  #   new_map = SU.tie(f.map, g.map, eq=None, nullValue=None)
  #   return NaiveFunction.mk_from_map(identifier, f.domain, f.codomain, new_map)

  @staticmethod
  def _compose_NaiveFunction(g: 'NaiveFunction[A, B]', f: 'NaiveFunction[A, B]', identifier: Optional[str] = None) -> 'NaiveFunction[A, B]':
    assert NaiveFunction._same_domain_codomain_values(f,g), f"{f=}\n{g=}"

    #FIXME TODO assert that the image of f (not including null) is a subset of the dod of g

    if identifier is None:
      identifier = f"{g.identifier}_of_{g.identifier}"

    new_map: Mapping[A, Optional[B]] = SU.compose(g, f, removeExplicitNulls=False, eq=None, nullValue=None)
    return NaiveFunction.mk_from_map(identifier, f.domain, f.codomain, new_map)

  @staticmethod
  def _thread_NaiveFunction(f: 'NaiveFunction[A, B]', g: 'NaiveFunction[A, B]', identifier: Optional[str] = None) -> 'NaiveFunction[A, B]':
    assert NaiveFunction._same_domain_codomain_values(f,g), f"{f=}\n{g=}"
    if identifier is None:
      identifier = f"{f.identifier}_then_{g.identifier}"

    return NaiveFunction._compose_NaiveFunction(f, g, identifier)


@eq.instance(NaiveFunction)
def _eq_NaiveFunction(left: NaiveFunction[A, B], right: NaiveFunction[A, B]) -> bool:
  return eq_defined_maps(left.map, right.map)



# TODO - change `PartialFunction` to `Relation`
@dataclass(frozen=True)
class SymbolicVectorRelation(SymbolicVectorSubset, PartialFunction, Generic[A, B]):
  # identifier: str
  domain    : ConcreteSort[A]
  codomain  : ConcreteSort[B]
  # map       : SymbolicVectorSubset[Tuple[A, B]]

  @staticmethod
  def _consistent_domain_codomain_universe( domain: ConcreteSort[A]
                                          , codomain: ConcreteSort[B]
                                          , universe: PairSeq
                                          ) -> bool:
    not_in_domain_sort   = lfilter( lambda k: k not in domain.values
                                  , map(fst, universe)
                                  )
    not_in_codomain_sort = lfilter( lambda k: k not in codomain.values
                                  , map(snd, universe)
                                  )
    assert len(not_in_domain_sort)   == 0, f"Domain values of universe missing from domain sort: '{not_in_domain_sort}'\ndomain={domain}\ncodomain={codomain}\nmap={map}"
    assert len(not_in_codomain_sort) == 0, f"Codomain values of universe missing from codomain sort: '{not_in_codomain_sort}'\ndomain={domain}\ncodomain={codomain}\nmap={map}"
    return True

  @staticmethod
  def _mk_domain_codomain_from_universe(identifier: str, universe: PairSeq) -> Tuple[ConcreteSort, ConcreteSort]:
    domain   = ConcreteSort( tuple(map( fst
                                      , universe
                                      )
                                  )
                           , f"{identifier}_dom"
                           )
    codomain = ConcreteSort( tuple(set(map( snd
                                          , universe
                                          )
                                      )
                                  )
                           , f"{identifier}_cod"
                           )
    return (domain, codomain)

  @staticmethod
  def _mk_universe_from_domain_codomain(domain: ConcreteSort[A], codomain: ConcreteSort[B]) -> PairSeq:
    return tuple(product(domain.values, codomain.values))

  @staticmethod
  def mk(identifier: str, universe: Union[PairSeq, Graph]) -> 'SymbolicVectorRelation[A,B]':  # type: ignore
    if isinstance(universe, set) or isinstance(universe, FrozenSet):  # type: ignore
      universe_t = tuple(sorted(universe))
    else:
      universe_t = universe
    domain, codomain            = SymbolicVectorRelation._mk_domain_codomain_from_universe(identifier, universe_t)
    map: Tuple[z3.BoolRef, ...] = SymbolicVectorRelation._mk_subset_tuple( len(universe_t)
                                                                         , identifier
                                                                         )
    return SymbolicVectorRelation(map, identifier, universe_t, domain, codomain)  # type: ignore
    # map_identifier = f"{identifier}_map"
    # map            = SymbolicVectorSubset.mk( identifier = map_identifier
    #                                         , universe   = universe
    #                                         )
    # return SymbolicVectorRelation(identifier, domain, codomain, map)

  @staticmethod
  def mk_from_domain_codomain(identifier: str, domain: ConcreteSort[A], codomain: ConcreteSort[B]) -> 'SymbolicVectorRelation[A,B]':
    universe: PairSeq           = SymbolicVectorRelation._mk_universe_from_domain_codomain(domain, codomain)
    map: Tuple[z3.BoolRef, ...] = SymbolicVectorRelation._mk_subset_tuple( len(universe)
                                                                         , identifier
                                                                         )
    return SymbolicVectorRelation(map, identifier, universe, domain, codomain)  # type: ignore

  # @staticmethod
  # def mk(identifier: str, domain: ConcreteSort[A], codomain: ConcreteSort[B]) -> 'SymbolicSetRelation[A,B]':
  #   universe: PairSeq = tuple(product(domain.values, codomain.values))
  #   map_identifier = f"{identifier}_map"
  #   map            = SymbolicVectorSubset.mk( identifier = map_identifier
  #                                           , universe   = universe
  #                                           )
  #   return SymbolicVectorRelation(identifier, domain, codomain, map)

  @staticmethod
  def mk_from_set(identifier: str, universe: PairSeq, s: Graph) -> Tuple['SymbolicVectorRelation[A,B]', Constraint]:  # type: ignore
    assert s.issubset(set(universe)), f"universe={universe}\ns={s}"

    domain, codomain            = SymbolicVectorRelation._mk_domain_codomain_from_universe(identifier, universe)
    map: Tuple[z3.BoolRef, ...] = SymbolicVectorRelation._mk_subset_tuple( len(universe)
                                                                         , identifier
                                                                         )
    ssv            = SymbolicVectorRelation(map, identifier, universe, domain, codomain)
    usv            = SymbolicVectorRelation._global_upper_bound_SymbolicVectorSubset(ssv)

    ssConstraints = is_subseteq(ssv, usv)
    eqConstraints = z3.And([ ssv.subset[i] if a in s else z3.Not(ssv.subset[i])
                             for i, a in enumerate(universe)
                           ])
    constraint    = z3.And(ssConstraints, eqConstraints)
    return (ssv, constraint)

  @staticmethod
  def mk_from_graph(identifier: str, universe: PairSeq, s: Graph) -> Tuple['SymbolicVectorRelation[A,B]', Constraint]:
    return SymbolicVectorRelation.mk_from_set(identifier, universe, s)

  @staticmethod
  def mk_from_pairs(identifier: str, universe: PairSeq, s: PairSeq) -> Tuple['SymbolicVectorRelation[A,B]', Constraint]:
    return SymbolicVectorRelation.mk_from_set(identifier, universe, frozenset(s))

  @staticmethod
  def mk_from_map(identifier: str, universe: PairSeq, s: Mapping[A, Optional[B]]) -> Tuple['SymbolicVectorRelation[A,B]', Constraint]:
    return SymbolicVectorRelation.mk_from_set(identifier, universe, frozenset(s.items()))

  @staticmethod
  def mk_from_tuple(identifier: str, universe: PairSeq, s: Tuple[bool, ...]) -> Tuple['SymbolicVectorRelation[A,B]', Constraint]:
    ensureSameLength(universe, s)

    domain, codomain            = SymbolicVectorRelation._mk_domain_codomain_from_universe(identifier, universe)
    map: Tuple[z3.BoolRef, ...] = SymbolicVectorRelation._mk_subset_tuple( len(universe)
                                                                         , identifier
                                                                         )
    ssv            = SymbolicVectorRelation(map, identifier, universe, domain, codomain)
    usv            = SymbolicVectorRelation._global_upper_bound_SymbolicVectorSubset(ssv)

    ssConstraints = is_subseteq(ssv, usv)
    eqConstraints = z3.And([ eq(ssv.subset[i], s[i])
                             for i, a in enumerate(universe)
                           ])
    constraint    = z3.And(ssConstraints, eqConstraints)
    return (ssv, constraint)

  @staticmethod
  def mk_from_NaiveSubset(identifier: str, universe: PairSeq, ns: NaiveSubset[Pair]) -> Tuple['SymbolicVectorRelation[A,B]', Constraint]:
    return SymbolicVectorRelation.mk_from_graph(identifier, universe, frozenset(ns.subset))

  @staticmethod
  def mk_from_NaiveFunction( function: NaiveFunction[A,B]
                           , identifier: Optional[str] = None
                           ) -> Tuple['SymbolicVectorRelation[A,B]', Constraint]:
    if identifier is None:
      identifier : str             = f"{function.identifier}_SVR"  # type: ignore
    domain       : ConcreteSort[A] = function.domain
    codomain     : ConcreteSort[B] = function.codomain
    universe     : PairSeq         = mk_graph1(function.map)
    map_graph_raw: Graph           = mk_graph(function.map)
    assert map_graph_raw.issubset(set(universe)), f"map_graph_raw={map_graph_raw}\nuniverse={universe}"

    ssv = SymbolicVectorRelation( SymbolicVectorRelation._mk_subset_tuple( len(universe)  # type: ignore
                                                                         , identifier  # type: ignore
                                                                         )
                                , identifier  # type: ignore
                                , universe
                                , domain
                                , codomain
                                )
    usv = SymbolicVectorRelation._global_upper_bound_SymbolicVectorSubset(ssv)

    ssConstraints = is_subseteq(ssv, usv)
    eqConstraints = z3.And([ ssv.subset[i] if a in map_graph_raw else z3.Not(ssv.subset[i])
                             for i, a in enumerate(universe)
                           ])
    constraint    = z3.And(ssConstraints, eqConstraints)
    return (ssv, constraint)

  def to_NaiveFunction(self, model: z3.ModelRef, identifier: Optional[str] = None) -> NaiveFunction[A, B]:
    if identifier is None:
      identifier = f"{self.identifier}_concrete"
    subset_concrete = frozenset(self.to_concreteSet(model))
    return NaiveFunction.mk_from_graph(identifier, self.domain, self.codomain, subset_concrete)

  # this constraint looks pretty rough
  @staticmethod
  def _is_functional( svr: 'SymbolicVectorRelation[A, B]'
                    , eq: Optional[Callable[[A, B], bool]] = None
                    , nullValue: Optional[bool] = None
                    ) -> Constraint:
    if eq is None:
      eq = _eq_as_function
    universe: PairSeq = svr.universe  # type: ignore
    universe_groupedBy_dom: Mapping[A, List[B]] = group_by(fst, universe)
    mutually_exclusive_groups: FrozenSet[Graph] = frozenset({ frozenset({ (d, c)
                                                                          for c in universe_groupedBy_dom[d]
                                                                          if not eq(c, nullValue)  # type: ignore
                                                                        })
                                                              for d in universe_groupedBy_dom
                                                            })

    def has_i_and_nothing_else_in(i: int, group_indices: FrozenSet[int]) -> Constraint:
      return z3.And([ svr.subset[j] if j == i else z3.Not(svr.subset[j])
                      for j in group_indices
                    ])
    def has_none_of(group_indices: FrozenSet[int]) -> Constraint:
      return z3.And([ z3.Not(svr.subset[j]) for j in group_indices ])

    def group_to_constraint(group: Graph) -> Constraint:
      group_indices: FrozenSet[int] = frozenset(map(universe.index, group))
      return z3.Or([ has_none_of(group_indices) ] + [ has_i_and_nothing_else_in(i, group_indices)
                                                      for i in group_indices
                                                    ])

    constraint = z3.And([ group_to_constraint(g)
                          for g in mutually_exclusive_groups
                        ])
    return constraint




@dataclass(frozen=True)
class SymbolicArrayFunction(PartialFunction, Generic[A, B]):
  identifier: str
  domain: SymbolicSort[A]
  codomain: SymbolicSort[B]
  map: z3Map

  @staticmethod
  def mk_fresh(identifier: str, dom: SymbolicSort[A], cod: SymbolicSort[B]) -> 'SymbolicArrayFunction[A,B]':
    return SymbolicArrayFunction( identifier
                                , dom
                                , cod
                                , z3.Array(identifier, dom, cod)
                                )

  @staticmethod
  def mk_from_NaiveFunction( f: NaiveFunction[A,B]
                           , identifier: Optional[str] = None
                           , dom_identifier: Optional[str] = None
                           , cod_identifier: Optional[str] = None
                           , dom_label: Callable[[A], str] = str
                           , cod_label: Callable[[B], str] = str
                           ) -> Tuple['SymbolicArrayFunction[A,B]', Constraint]:
    if identifier is None:
      identifier = f.identifier
    if dom_identifier is None:
      # dom_identifier = f"{identifier}_dom_symbolic"
      dom_identifier = f"{f.domain.identifier}_symbolic"
    if cod_identifier is None:
      # cod_identifier = f"{identifier}_cod_symbolic"
      cod_identifier = f"{f.codomain.identifier}_symbolic"

    domain   = SymbolicSort.mk_from_ConcreteSort(f.domain  , dom_identifier, dom_label)
    codomain = SymbolicSort.mk_from_ConcreteSort(f.codomain, cod_identifier, cod_label)

    saf = SymbolicArrayFunction( identifier
                               , domain
                               , codomain
                               , z3.Array(identifier, domain.sort, codomain.sort)
                               )
    saf_constraint = z3.And([ saf.map[domain.values_constants[a]] == codomain.values_constants[b]
                              for a,b in f.pairs
                            ])
    return (saf, saf_constraint)

  def to_concreteMap(self, model: z3.ModelRef) -> Mapping[A, Optional[B]]:
    return mk_map_from_SymbolicArray(model, self.map, self.domain, self.codomain)  # type: ignore

  def to_NaiveFunction(self, model: z3.ModelRef, identifier: Optional[str] = None) -> NaiveFunction[A, B]:
    if identifier is None:
      identifier = f"{self.identifier}_concrete"
    return NaiveFunction.mk_from_map( identifier
                                    , self.domain.to_ConcreteSort()
                                    , self.codomain.to_ConcreteSort()
                                    , self.to_concreteMap(model)
                                    )
