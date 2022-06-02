'''
The garbage pile.
'''

from dataclasses import dataclass
from typing import TypeVar, Generic, Optional, Union, \
  Collection, Sequence, Reversible, Callable, \
  Tuple, List, FrozenSet, Set, Any, Dict, Mapping
# from random import randint, sample#, shuffle, choice, choices

from pyrsistent import m, pmap
# from collections import defaultdict

#from copy import deepcopy
from functools import reduce
from itertools import product
from more_itertools import peekable

# `funcy` provides some convenient functionally-flavored combinators for manipulating collections and
# dictionaries used throughout: https://funcy.readthedocs.io/en/stable/index.html
from funcy import walk, lmap, group_by, lfilter

import bidict as bd
from bidict import frozenbidict as bid

import z3



# type variables

A = TypeVar('A')
B = TypeVar('B')
C = TypeVar('C')
S = TypeVar('S')
V = TypeVar('V')



# the identity map

def identity(a: A) -> A:
  return a



# z3

def getModel(constraints):
  solver = z3.Solver()
  solver.add(*constraints)

  if solver.check() == z3.sat:
    return solver.model(), solver
  else:
    return None, solver



# Type aliases and functions related to defining custom datatypes in z3 and
# modeling functions using the theory of arrays

z3Sort         = z3.DatatypeSortRef
z3Sorts        = List[z3.DatatypeSortRef]
z3Constant     = z3.DatatypeSortRef
z3Constants    = List[z3.DatatypeSortRef]
z3Map          = z3.ArrayRef


def mk_EnumRef(identifier: str, values: Tuple[A, ...], label: Callable[[A], str]) -> Tuple[z3.DatatypeSortRef, z3Constants]:
  """
  Given
   - a name `identifier` for a new z3 sort
   - a tuple `values` of unique values for the sort
   - a function `label` for mapping each value to a unique (preferably human-readable) label
  this returns a DatatypeSortRef using `EnumSort`.
  """
  assert len(values) == len(set(values)), f"identifier='{identifier}'\nt='{values}'"
  labels = lmap(label, values)
  assert len(set(labels)) == len(values), f"identifier='{identifier}'\nt='{values}'\nlabels='{labels}'"
  return z3.EnumSort(identifier, labels)


# Custom types (intended to be a sum type) that allow for useful introspection
# and bookkeeping on symbolic representations of partial functions (like feature
# vectors).

@dataclass(frozen=True)
class Sort(Generic[A]):
  values: Tuple[A, ...]

  # @staticmethod
  # def restrictTo(restriction: Set[A]):

@dataclass(frozen=True)
class ConcreteSort(Sort, Generic[A]):
  identifier: str

@dataclass(frozen=True)
class SymbolicSort(Sort, Generic[A]):
  identifier: str
  sort: z3.DatatypeRef  # `z3Sort`
  constants: Tuple[z3.DatatypeRef, ...]  # `z3Constant`
  label: Callable[[A], str]
  labels: Tuple[str, ...]
  values_labels: bid[A, str]
  values_constants: bid[A, z3Constant]
  constants_labels: bid[z3Constant, str]

  @staticmethod
  def _consistent(s: 'SymbolicSort[A]') -> bool:
    assert areSameLength( s.values, s.constants )
    assert areSameLength( s.values, s.labels )

    assert set(s.values)    == set(s.values_labels.keys())
    assert set(s.values)    == set(s.values_constants.keys())
    assert set(s.labels)    == set(s.values_labels.values())
    assert set(s.labels)    == set(s.constants_labels.values())
    assert set(s.constants) == set(s.constants_labels.keys())
    assert set(s.constants) == set(s.values_constants.values())

    assert s.labels == tuple(lmap(s.label, s.values)), f"labels={labels} vs. '{tuple(lmap(s.label, s.values))}'\ns={s}"  # type: ignore

    for v in s.values_labels:
      l_from_v  = s.values_labels[v]
      c_from_v  = s.values_constants[v]
      l_from_vc = s.constants_labels[c_from_v]
      assert l_from_v == l_from_vc, f"v={v}\nl_from_v={l_from_v}\nc_from_v={c_from_v}\nl_from_vc={l_from_vc}\ns={s}"

    return True

  @staticmethod
  def mk(values: Tuple[A, ...], identifier: str, label: Callable[[A], str]) -> 'SymbolicSort[A]':
    """
    Given
    - a tuple `values` of unique values of type `A` for the sort
    - a name `identifier` for a new z3 sort
    - a function `label` for mapping each value to a unique (preferably human-
      readable) label
    return a corresponding `SymbolicSort[A]`
    """
    enumRef, constants = mk_EnumRef(identifier, values, label)
    constants_t = tuple(constants)
    labels = tuple(lmap(label, values))

    values_labels    = bid(zip(values, labels))
    values_constants = bid(zip(values, constants_t))
    constants_labels = bid(zip(constants_t, labels))

    return SymbolicSort( values = values
                       , identifier = identifier
                       , sort = enumRef
                       , constants = constants_t
                       , label = label
                       , labels = labels
                       , values_labels = values_labels
                       , values_constants = values_constants
                       , constants_labels = constants_labels
                       )

  @staticmethod
  def mk_from_ConcreteSort(values: ConcreteSort[A], identifier: Optional[str] = None, label: Callable[[A], str] = str) -> 'SymbolicSort[A]':
    if identifier is None:
      identifier = f"{values.identifier}_symbolic"
    return SymbolicSort.mk(values.values, identifier, label)

  def to_ConcreteSort(self, identifier: Optional[str] = None) -> ConcreteSort[A]:
    if identifier is None:
      identifier = f"{self.identifier}_concrete"
    return ConcreteSort(self.values, identifier)


  def Val(self, identifier: str):
    """
    Create a reference to a z3 variable of this sort.

    Comparable to `p = z3.Bool("p")` but for this sort instead of `z3.BoolRef`.
    """
    return z3.Const(identifier, self.sort)

def mk_map_from_SymbolicArray( model: z3.ModelRef
                             , array: z3.ArrayRef
                             , domain_sort: SymbolicSort[A]
                             , codomain_sort: SymbolicSort[B]
                             ) -> Mapping[A, Optional[B]]:
  array_solution = model[array]
  # m = dict()
  # for d in domain_sort.values:
  #   d_const = domain_sort.values_constants[d]
  #   c_const = array_solution[d_const]
  #   # assert c_const in codomain_sort.values_constants.inv.keys(), f"{c_const=}\n{z3.simplify(c_const)}"
  #   assert z3.simplify(c_const) in codomain_sort.values_constants.inv.keys(), f"{c_const=}\n{z3.simplify(c_const)}"
  #   c_const_simplified = z3.simplify(c_const)
  #   try:
  #     c       = codomain_sort.values_constants.inv[z3.simplify(c_const)]
  #   except Exception:
  #     print(f"{codomain_sort=}")
  #     print(f"{codomain_sort.values_constants.inv=}")
  #     print(f"{d=}")
  #     print(f"{d_const=}")
  #     print(f"{c_const=}")
  #     print(f"{array_solution=}")
  #     raise Exception
  #   m[d] = c
  # return pmap(m)
  return pmap({ d : codomain_sort.values_constants.inv[ z3.simplify( array_solution[ domain_sort.values_constants[d] ]) ]
                for d in domain_sort.values
              })



Pair    = Tuple[A, Optional[B]]
PairSeq = Tuple[Pair, ...]
Graph   = FrozenSet[Pair]

def mk_map_from_function_over(f: Callable[[A], Optional[B]]
                             , values: Set[A]
                             , raiseErrors: bool = False
                             , eq: Optional[Callable[[A, B], bool]] = None
                             , nullValue: Optional[B] = None
                             ) -> Mapping[A, B]:
  if raiseErrors:
    return pmap({v:f(v) for v in values})
  else:
    map = dict()

    for v in values:
      try:
        out = f(v)
      except:
        out = None

      if out is None:
        map[v] = nullValue
      else:
        map[v] = out

    return pmap(map)

def mk_function_from_map(map: Mapping[A, B], nullValue: Optional[B] = None) -> Callable[[A], Optional[B]]:
  def f(a: A) -> Optional[B]:
    return map.get(a, nullValue)
  return f

def mk_graph(map: Mapping[A, B]) -> FrozenSet[Tuple[A, B]]:
  return frozenset(map.items())

def mk_graph1(map: Mapping[A, B]) -> Tuple[Tuple[A, B], ...]:
  return tuple(map.items())

def is_functional(graph: Graph, eq: Optional[Callable[[A, B], bool]] = None, nullValue = None) -> bool:
  if eq is None:
    eq = _eq_as_function
  universe = tuple(graph)
  universe_groupedBy_dom: Mapping[A, List[B]] = group_by(fst, universe)
  return any(lmap( lambda image: len(lfilter( lambda a: not eq(a, nullValue)
                                       , image
                                       )
                                ) > 1
                  , universe_groupedBy_dom.values()
                  ))

def compose( g: Mapping[B, C]
           , f: Mapping[A, B]
           , removeExplicitNulls = False
           , eq: Optional[Callable[[A, B], bool]] = None
           , nullValue: Optional[Union[B, C]] = None
           ) -> Mapping[A, Optional[C]]:
  if eq is None:
    eq = _eq_as_function
  # return {a:g[f[a]] for a in f}
  def include(a: A) -> bool:
    if not removeExplicitNulls:
      return True
    f_defined_at_a  = is_defined(f.get(a), eq, nullValue)  # type: ignore
    g_defined_at_fa = is_defined(g.get(f.get(a)), eq, nullValue)  # type: ignore
    return f_defined_at_a and g_defined_at_fa
  return pmap({ a: g.get( f.get(a) )  # type: ignore
                for a in f
                if include(a)
                # if (not removeExplicitNulls) \
                # or ( removeExplicitNulls \
                #   and is_defined(f.get(a), eq, nullValue) \
                #   and is_defined(g.get(f.get(a)), eq, nullValue)  # type: ignore
                #   )  # type: ignore
              })

def thread( f: Mapping[A, B]
          , g: Mapping[B, C]
          , removeExplicitNulls = False
          , eq: Optional[Callable[[A, B], bool]] = None
          , nullValue: Optional[Union[B, C]] = None
          ) -> Mapping[A, Optional[C]]:
  return compose(g, f, removeExplicitNulls, eq, nullValue)

def override( left: Mapping[A, B]
            , right: Mapping[A, B]
            , eq: Optional[Callable[[A, B], bool]] = None
            , nullValue: Optional[A] = None
            ) -> Mapping[A, B]:
  """
  `override` operation `l ◀ r` from e.g. Cirulis (2011):
   - read as: "`r` overrides `l`"
   - synonym for "right priority union"
  """
  if eq is None:
    eq = _eq_as_function
  return pmap({ k : right[k] if k in right.keys() and not eq(nullValue, right[k]) else left[k]  # type: ignore
                for k in frozenset(left.keys()).union(frozenset(right.keys()))
              })

def prunion( left: Mapping[A, B]
           , right: Mapping[A, B]
           , eq: Optional[Callable[[A, B], bool]] = None
           , nullValue: Optional[A] = None
           ) -> Mapping[A, B]:
  """
  Right priority union.
  """
  return override(right, left, eq, nullValue)

def all_partial_map_codomains(domain_size: int, codomain: FrozenSet[B]) -> Tuple[Optional[B], ...]:
  assert domain_size >= 0, f"domain_size={domain_size}"
  return tuple(product( codomain.union({None})  # type: ignore
                      , repeat=domain_size
                      ))

def all_partial_maps(domain: FrozenSet[A], codomain: FrozenSet[B]) -> Tuple[Tuple[Tuple[A, Optional[B]], ...], ...]:
  domain_t = tuple(sorted(domain))  # type: ignore
  return tuple(map(lambda codomain: tuple(zip( domain_t
                                        , codomain
                                        ))
                  , product( codomain.union({None})  # type: ignore
                           , repeat=len(domain_t)
                           )
                  ))

def _eq_as_function(a: Optional[A], b: Optional[B]) -> bool:
  return a == b

def is_undefined(a: Optional[A], eq: Optional[Callable[[A, B], bool]] = None, nullValue: Optional[A] = None) -> bool:
  if eq is None:
    eq = _eq_as_function
  return a is None or eq(a, nullValue)  # type: ignore

def is_defined(a: Optional[A], eq: Optional[Callable[[A, B], bool]] = None, nullValue: Optional[A] = None) -> bool:
  if eq is None:
    eq = _eq_as_function
  return not is_undefined(a, eq, nullValue)

def is_defined_at(f: Mapping[A, Optional[B]], a: A, eq: Optional[Callable[[A, B], bool]] = None, nullValue: Optional[B] = None) -> bool:
  if eq is None:
    eq = _eq_as_function
  return is_defined(f.get(a, nullValue), eq, nullValue)  # type: ignore

def has_explicit_nullMaps(f: Mapping[A, Optional[B]], eq: Optional[Callable[[A, B], bool]] = None, nullValue: Optional[B] = None) -> bool:
  if eq is None:
    eq = _eq_as_function
  return None in f.values() or any([eq(nullValue, v) for v in f.values()])  # type: ignore

def drop_explicit_nullMaps(f: Mapping[A, Optional[B]], eq: Optional[Callable[[A, B], bool]] = None, nullValue: Optional[B] = None) -> Mapping[A, Optional[B]]:
  if eq is None:
    eq = _eq_as_function
  return pmap({k:v for k,v in f.items() if not eq(v, nullValue)})  # type: ignore

def pad_with_explicit_nullMaps(f: Mapping[A, Optional[B]], domain_to_pad: FrozenSet[A], nullValue: Optional[B] = None) -> Mapping[A, Optional[B]]:
  return pmap({k:f.get(k, nullValue) for k in domain_to_pad.union(frozenset(f.keys()))})

def dod(f: Mapping[A, Optional[B]], eq: Optional[Callable[[A, B], bool]] = None, nullValue: Optional[B] = None) -> Tuple[A, ...]:
  """
  Return the **domain of definition** of `f`
  """
  if eq is None:
    eq = _eq_as_function
  return tuple(filter( lambda k: is_defined_at(f, k, eq, nullValue)
                     , f.keys()))

def common_dod( left: Mapping[A, Optional[B]]
              , right: Mapping[A, Optional[B]]
              , eq: Optional[Callable[[A, A], bool]] = None
              , nullValue: Optional[B] = None
              ) -> FrozenSet[A]:
  if eq is None:
    eq = _eq_as_function
  return frozenset({ l
                     for l in dod(left, eq, nullValue)  # type: ignore
                     if any([eq(l, r) for r in dod(right, eq, nullValue)])  # type: ignore
                   })
 # return frozenset(dom_def(left, nullValue)).intersection(frozenset(dom_def(right, nullValue)))

def eq_dod( left: Mapping[A, Optional[B]]
          , right: Mapping[A, Optional[B]]
          , eq: Optional[Callable[[A, A], bool]] = None
          , nullValue: Optional[B] = None
          ) -> FrozenSet[A]:
  if eq is None:
    eq = _eq_as_function
  left_dod  = dod(left, nullValue)  # type: ignore
  right_dod = dod(right, nullValue)  # type: ignore
  left_right_dod = common_dod(left, right, eq, nullValue)
  return left_right_dod == frozenset(left_dod) and left_right_dod == frozenset(right_dod)  # type: ignore

def equalizer( left: Mapping[A, Optional[B]]
             , right: Mapping[A, Optional[B]]
             , eq: Optional[Callable[[A, A], bool]] = None
             , nullValue: Optional[B] = None
             ) -> FrozenSet[A]:
  if eq is None:
    eq = _eq_as_function
  return frozenset({ a
                     for a in common_dod(left, right, eq, nullValue)
                     if eq(left[a], right[a])  # type: ignore
                   })

def tie( left: Mapping[A, Optional[B]]
       , right: Mapping[A, Optional[B]]
       , eq: Optional[Callable[[A, A], bool]] = None
       , nullValue: Optional[B] = None
       ) -> Mapping[A, Optional[B]]:
  if eq is None:
    eq = _eq_as_function
  lr_equalizer = equalizer(left, right, eq, nullValue)
  tie_dod   = frozenset(filter( lambda k: not any([eq(k, e) for e in lr_equalizer])  # type: ignore
                              , frozenset(left.keys()).union(frozenset(right.keys()))
                              )
                       )
  return pmap({t:t for t in tie_dod})

def fixmaps( f: Mapping[A, Optional[B]]
           , eq: Optional[Callable[[A, A], bool]] = None
           , nullValue: Optional[B] = None
           ) -> Mapping[A, Optional[B]]:
  if eq is None:
    eq = _eq_as_function
  return pmap({k:v for k,v in f.items() if eq(k, v)})  # type: ignore

def fixpoints( f: Mapping[A, Optional[B]]
             , eq: Optional[Callable[[A, A], bool]] = None
             , nullValue: Optional[B] = None
             ) -> FrozenSet[A]:
  if eq is None:
    eq = _eq_as_function
  return frozenset(fixmaps(f, eq, nullValue).keys())

def mumaps( f: Mapping[A, Optional[B]]
          , eq: Optional[Callable[[A, A], bool]] = None
          , nullValue: Optional[B] = None
          ) -> Mapping[A, Optional[B]]:
  if eq is None:
    eq = _eq_as_function
  return pmap({k:v for k,v in f.items() if not eq(k, v)})  # type: ignore

def mupoints( f: Mapping[A, Optional[B]]
            , eq: Optional[Callable[[A, A], bool]] = None
            , nullValue: Optional[B] = None
            ) -> FrozenSet[A]:
  if eq is None:
    eq = _eq_as_function
  return frozenset(mumaps(f, eq, nullValue).keys())

def eq_defined_maps( left: Mapping[A,Optional[B]]
                   , right: Mapping[A, Optional[B]]
                   , eq: Optional[Callable[[A, A], bool]] = None
                   , nullValue: Optional[B] = None
                   ) -> bool:
  left_right_dod = common_dod(left, right, eq, nullValue)
  if not eq_dod(left, right, eq, nullValue):
    return False
  left_right_equalizer = equalizer(left, right, eq, nullValue)
  return left_right_dod == left_right_equalizer



# To aid in generating fresh names.
# Simplest, dumbest implementation.
# More helpful for making constraint graphs interpretable would be sampling a few random (short!) words
def freshGenerator():
  start = 0
  while True:
    yield f"{start}" # no int provided (just str) because it should not be a source of global ordering!
    start += 1

def isNonnull(x: Any) -> bool:
  return x is not None

def ensureNonnull(x: Any, msg: Optional[str] = None) -> bool:
  if x is None:
    if msg is None:
      raise TypeError(f"x={x} must be non-null.")
    else:
      raise TypeError(msg)
  return True

def ensureNull(x: Any, msg: Optional[str] = None) -> bool:
  if isNonnull(x):
    if msg is None:
      raise TypeError(f"x={x} should be null.")
    else:
      raise TypeError(msg)
  return True



# SEQUENCES

def foldl(binOp: Callable[[A,B], A], initial: Optional[A] = None):
  def f(values: Sequence[B]) -> A:
    if initial is None:
      return reduce(binOp, values)  # type: ignore
    else:
      return reduce(binOp, values, initial)
  return f

def zipWith(binOp: Callable[[A,B], C], a: Sequence[A], b: Sequence[B]) -> Sequence[C]:
  return walk( lambda pair: binOp(*pair)
             , zip(a,b)
             )

def peek(xs: Collection[A]) -> Optional[A]:
  return None if len(xs) == 0 else peekable(xs).peek()

def pi(i: int):
  assert i > -1, f"{i}"
  def projection(seq: Sequence[A]) -> A:
    assert len(seq) > i
    return seq[i]
  return projection

def p0(seq: Sequence[A]) -> A:
  return pi(0)(seq)

def p1(seq: Sequence[A]) -> A:
  return pi(1)(seq)

def p2(seq: Sequence[A]) -> A:
  return pi(2)(seq)

def fst(seq: Sequence[A]) -> A:
  return p0(seq)

def snd(seq: Sequence[A]) -> A:
  return p1(seq)

def thrd(seq: Sequence[A]) -> A:
  return p2(seq)



# PREDICATES / ASSERTIONS ABOUT SEQUENCES AND COLLECTIONS


def areOrdered(collection: Union[Sequence, Reversible]) -> bool:
  return isinstance(collection, Sequence) or isinstance(collection, Reversible)

def areSameLength(a: Sequence, b: Sequence) -> bool:
  return len(a) == len(b)

def areSameLengths(seqs: Sequence[Sequence]) -> bool:
  L = len(seqs[0])
  return all([len(each) == L for each in seqs])

def isEmpty(collection: Collection) -> bool:
  return len(collection) == 0

def isNonempty(collection: Collection) -> bool:
  return len(collection) > 0

def ensureOrdered(collection: Union[Sequence, Reversible]):
  assert areOrdered(collection), f"collection expected to be an instance of either Sequence or Reversible.\nType: {type(collection)}\ncollection: {collection}"

def ensureSameLength(a: Sequence, b: Sequence):
  assert areSameLength(a, b), f"{len(a)} != {len(b)}"

def ensureSameLengths(seqs: Sequence[Sequence]):
  assert areSameLengths(seqs), f"lengths not homogenous: {lmap(len, seqs)}\nseqs={seqs}"

def lines(args: Sequence[str], sep="\n") -> str:
  return sep.join(args)


# Error handling


def mk_Boolean_OverloadingError(left: Collection, right: Any) -> Exception:
  return Exception("left is a collection but right is not None:\nleft = '{left}'\nright = '{right}'")

def mk_Boolean_OverloadingError1(t) -> Exception:
  return Exception(f"left is a {t} but right is None")

def mk_Boolean_TypeParameterError(arg: Collection, expectedType) -> Exception:
  return Exception(f"arg is a Collection but not of expected type `{expectedType}`:\narg = '{arg}'")

def mk_UnknownTypeError(value: Any, expectedTypes: Optional[list]) -> Exception:
  msg = f"Unhandled type '{type(value)}'"
  if expectedTypes is not None:
    suffix = f"\nExpected one of: {expectedTypes}"
  else:
    suffix = ""
  return Exception(msg + suffix)
