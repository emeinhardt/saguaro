
from typing import Optional, Union
from typing import Callable, Mapping, \
                   Collection, Sequence, \
                   Tuple, List, \
                   Set, FrozenSet

import hypothesis
from hypothesis import given, settings
from hypothesis import strategies as st
from hypothesis.strategies import SearchStrategy

from funcy import lmap, lmapcat, lfilter, project, omit

from pyrsistent import pmap
from bidict import frozenbidict as fid

import z3

import saguaro.utilities as SU
import saguaro._Boolean as SB
import saguaro.Eq as SE
import saguaro.Order as SO
import saguaro.Subset as SS

from saguaro.utilities import foldl, peek
from saguaro.utilities import A, B, getModel, fst, snd, identity
from saguaro.utilities import z3Sort, z3Constant, z3Map
from saguaro.utilities import Sort, ConcreteSort, SymbolicSort#, mk_EnumRef
from saguaro.utilities import mk_map_from_function_over, mk_function_from_map, \
                              mk_graph, mk_graph1, all_partial_maps, \
                              compose, override, prunion, \
                              is_undefined, is_defined, is_defined_at, \
                              has_explicit_nullMaps, drop_explicit_nullMaps, \
                              pad_with_explicit_nullMaps, \
                              dod, common_dod, eq_dod, \
                              eq_defined_maps, equalizer, tie, \
                              fixmaps, mumaps, fixpoints, mupoints
from saguaro._Boolean import Bool, Constraint, Constraints, \
                             id_Bool, \
                             bool_to_BoolRef1
from saguaro._Boolean import Not, Not1, \
                             And, And1, \
                             Or, Or1, \
                             Implies, Implies1, \
                             Iff, Iff1, \
                             _strategy_bool, _strategy_BoolRef
from saguaro.Eq import Eq, eq, eq1, eq2, eq3, eq4, eq5, neq, neq1
from saguaro.Order import _enumerate_Preorder, _ConcreteEnumeration
from saguaro.Order import le, ge, lt, gt, lt1, gt1, \
                          comparable, is_between, is_in_interval, \
                          is_minimal, is_maximal, is_least, is_greatest, \
                          is_lower_bound, is_upper_bound, \
                          is_least_upper_bound, is_least_upper_bound1, \
                          is_greatest_lower_bound, is_greatest_lower_bound1, \
                          has_least_upper_bound, has_least_upper_bound1, \
                          has_greatest_lower_bound, has_greatest_lower_bound1, \
                          is_join, is_join1, \
                          is_meet, is_meet1, \
                          has_join, has_join1, \
                          has_meet, has_meet1, \
                          covers, is_chain, \
                          is_atom, is_atom1, \
                          global_lower_bound, global_upper_bound, \
                          is_global_lower_bound, is_global_upper_bound, \
                          complementary
# from saguaro.Order import law_reflexivity_forAll, law_transitivity_forAll
from saguaro.Order import law_lowerBounded, law_upperBounded, \
                          law_antisymmetric_forAll, \
                          law_meetExists_forAll, law_joinExists_forAll, \
                          law_complementExists_forAll, \
                          law_meetDistributesOverJoin_forAll
# from saguaro.Order import law_meetDistributesOverJoin_rel_forAll
from saguaro.Map import NaiveFunction, SymbolicVectorRelation, SymbolicArrayFunction
# from saguaro.Map import ???

def test_should_pass():
  assert False == False

# def test_should_fail():
#   assert False == True

#################
# CONSTANT DATA #
#################

D2     = ("-", "+")
D2plus = ("-", "+", None)
D2_concrete     = ConcreteSort(D2, "D2")
D2plus_concrete = ConcreteSort(D2plus, "D2+")
D2_symbolic     = SymbolicSort.mk(D2, "D2", identity)
D2plus_symbolic = SymbolicSort.mk(D2plus, "D2+",  str)
D2_maps_pairs: Tuple[Tuple[Tuple[str, Optional[str]], ...], ...] = all_partial_maps(frozenset(D2), frozenset(D2))
D2_maps_dicts: Tuple[Mapping[str, Optional[str]], ...] = tuple(map(pmap, D2_maps_pairs))

# SYMBOLS = fid({ "FILLED_SQUARE"         : "■"
#               , "BLANK_SQUARE"          : "□"
#               , "FILLED_DIAMOND"        : "◆"
#               , "BLANK_DIAMOND"         : "◇"
#               , "FILLED_CIRCLE"         : "●"
#               , "BLANK_CIRCLE"          : "○"
#               , "FILLED_TRIANGLE_UP"    : "▲"
#               , "BLANK_TRIANGLE_UP"     : "△"
#               , "FILLED_TRIANGLE_DOWN"  : "▼"
#               , "BLANK_TRIANGLE_DOWN"   : "▽"
#               , "FILLED_TRIANGLE_LEFT"  : "◀"
#               , "BLANK_TRIANGLE_LEFT"   : "◁"
#               , "FILLED_TRIANGLE_RIGHT" : "▶"
#               , "BLANK_TRIANGLE_RIGHT"  : "▷"
#               , "FILLED_PENTAGON"       : "⬟"
#               , "BLANK_PENTAGON"        : "⬠"
#               , "FILLED_HEXAGON"        : "⬢"
#               , "BLANK_HEXAGON"         : "⬡"
#               })
# FILLS        = ("FILLED", "BLANK")
# SHAPES       = ("SQUARE", "DIAMOND", "CIRCLE", "TRIANGLE", "PENTAGON", "HEXAGON")
# ORIENTATIONS = ("UP", "DOWN", "LEFT", "RIGHT")
# CLASSES = { k:project( SYMBOLS
#                      , lfilter(lambda name: k in name, SYMBOLS.keys())
#                      )
#             for k in lmapcat( list
#                             , (FILLS, SHAPES, ORIENTATIONS)
#                             )
#           }

# twoD2 = project( SYMBOLS
#                , lfilter( lambda name: "SQUARE" in name or "CIRCLE" in name
#                         , SYMBOLS.keys()
#                         )
#                )
# oneD3 = project( SYMBOLS
#                  , lfilter( lambda name: "FILLED" in name
#                                     and any([ k in name
#                                             for k in ("SQUARE", "CIRCLE", "TRIANGLE_UP")
#                                           ])
#                           , SYMBOLS.keys()
#                           )
#                )

# twoD2_concrete = ConcreteSort(tuple(sorted(twoD2.values())))
# oneD3_concrete = ConcreteSort(tuple(sorted(oneD3.values())))
# twoD2_symbolic = SymbolicSort.mk(tuple(sorted(twoD2.values())), "twoD2",  identity)
# oneD3_symbolic = SymbolicSort.mk(tuple(sorted(oneD3.values())), "oneD3",  identity)



def test_Map_basic_SymbolicSort():
  # assert SymbolicSort._consistent(twoD2_symbolic)
  # assert SymbolicSort._consistent(oneD3_symbolic)
  assert SymbolicSort._consistent(D2_symbolic)
  assert SymbolicSort._consistent(D2plus_symbolic)

def test_NaiveFunction_mk_from_map():
  D2_maps_NF_from_dicts: Set[NaiveFunction] = set()
  for i,map in enumerate(D2_maps_dicts):
    D2_maps_NF_from_dicts.add(NaiveFunction.mk_from_map(f"D2_maps_fromDict_{i}_NF", D2_concrete, D2plus_concrete, map))

def test_Map_NaiveFunction_mk_from_pairs():
  D2_maps_NF_from_pairs = set()
  for i,pairs in enumerate(D2_maps_pairs):
    D2_maps_NF_from_pairs.add(NaiveFunction.mk_from_pairs(f"D2_maps_fromPairs_{i}_SVR", D2_concrete, D2plus_concrete, pairs))

def test_SymbolicVectorRelation_mk_from_pairs():
  D2_maps_SVR_from_pairs: Set[Tuple[SymbolicVectorRelation, Constraint]] = set()
  D2_maps_pairs_universe = SymbolicVectorRelation._mk_universe_from_domain_codomain(D2_concrete, D2plus_concrete)
  for i,pairs in enumerate(D2_maps_pairs):
    D2_maps_SVR_from_pairs.add(SymbolicVectorRelation.mk_from_pairs(f"D2_maps_fromPairs_{i}_SVR", D2_maps_pairs_universe, pairs))

# def test_SymbolicVectorRelation_mk_from_tuple(): ...

# def test_SymbolicVectorRelation_mk_from_NaiveSubset(): ...

# def test_SymbolicVectorRelation_mk_from_NaiveFunction(): ...

# def test_SymbolicArrayFunction_mk_from_NaiveFunction(): ...

def test_SymbolicVectorRelation_NaiveFunction_roundtrip():
  D2_maps_NF_from_dicts = [ NaiveFunction.mk_from_map( f"D2_maps_fromDict_{i}_NF"
                                                     , D2_concrete
                                                     , D2plus_concrete
                                                     , map
                                                     )
                            for i,map in enumerate(D2_maps_dicts)
                          ]
  D2_maps_SVR: List[Tuple[SymbolicVectorRelation, Constraint]] = list()
  for i, nf in enumerate(D2_maps_NF_from_dicts):
    D2_maps_SVR.append(SymbolicVectorRelation.mk_from_NaiveFunction(nf, f"D2_maps_fromNF_{i}_SVR"))

  for i, svr_and_con in enumerate(D2_maps_SVR):
    svr, svr_con = svr_and_con
    model, _ = getModel([svr_con])
    if model is not None:
      nf_out = svr.to_NaiveFunction(model)
      assert eq(nf_out, D2_maps_NF_from_dicts[i]), f"i={i}\nmap={D2_maps_dicts[i]}\nnf_in={D2_maps_NF_from_dicts[i]}\nnf_out={nf_out}\nsvr={svr_and_con[0]}\nsvr_con={svr_and_con[1]}"


def test_SymbolicArrayFunction_NaiveFunction_roundtrip():
  D2_maps_NF_from_dicts = [ NaiveFunction.mk_from_map( f"D2_maps_fromDict_{i}_NF"
                                                     , D2_concrete
                                                     , D2plus_concrete
                                                     , map
                                                     )
                            for i,map in enumerate(D2_maps_dicts)
                          ]
  D2_maps_SAF: List[Tuple[SymbolicArrayFunction, Constraint]] = list()
  for i, nf in enumerate(D2_maps_NF_from_dicts):
    D2_maps_SAF.append(SymbolicArrayFunction.mk_from_NaiveFunction(nf, f"D2_maps_fromNF_{i}_SAF"))

  for i, saf_and_con in enumerate(D2_maps_SAF):
    saf, saf_con = saf_and_con
    model, _ = getModel([saf_con])
    if model is not None:
      nf_out = saf.to_NaiveFunction(model)
      assert eq(nf_out, D2_maps_NF_from_dicts[i]), f"i={i}\nmap={D2_maps_dicts[i]}\nnf_in={D2_maps_NF_from_dicts[i]}\nnf_out={nf_out}\nsaf={saf_and_con[0]}\nsaf_con={saf_and_con[1]}"


# TODO
# def test_SymbolicVectorRelation_is_functional():
#   # construct fresh relation,
#   # assert it's functional,
#   # concretize it,
#   # and verify the result is functional
#   ...

# TODO - test typeclass instances for NaiveFunction

# TODO - test consistency for typeclass instances of SymbolicVectorRelation
#  - start with key ones related to changes relative to SymbolicVectorSubset
#    - Eq
#    - Nearlattice
#    - OverridingNearlattice
#    - BooleanNearlattice
# Eq

# @given(_strategy_NaiveFunction_FV3())
# def test_SymbolicVectorRelation_Eq_law_reflexivity_forAll(f: NaiveFunction[F3, Bplus]):
#   assert check_consistency_one( SE.law_reflexivity_forAll, f, f_is_unique_solution=False)

# @given(_strategy_NaiveFunction_FV3(), _strategy_NaiveFunction_FV3(), _strategy_NaiveFunction_FV3())
# def test_SymbolicVectorRelation_Eq_law_transitivity_forAll(f: NaiveFunction[F3, Bplus], left: NaiveFunction[F3, Bplus], right: NaiveFunction[F3, Bplus]):
#   assert check_consistency_oneOneOne( SE.law_transitivity_forAll, f, left, right, f_is_unique_solution=False, addFinalNullPSArg=False)

# @given(_strategy_NaiveFunction_FV3(), _strategy_NaiveFunction_FV3())
# def test_SymbolicVectorRelation_Eq_law_symmetry_forAll(left: NaiveFunction[F3, Bplus], right: NaiveFunction[F3, Bplus]):
#   assert check_consistency_oneOne( SE.law_symmetry_forAll, left, right, left_is_unique_solution=False)

# Nearlattice

# @given(_strategy_NaiveFunction_FV3(), _strategy_NaiveFunction_FV3(), _strategy_NaiveFunction_FV3_Free())
# def test_SymbolicVectorRelation_Nearlattice_law_upperBoundProperty_forAll(left: NaiveFunction[F3, Bplus], right: NaiveFunction[F3, Bplus], ps: Set[NaiveFunction[F3, Bplus]]):
#   assert check_consistency_oneOneMany( law_upperBoundProperty_forAll, left, right, ps, left_is_unique_solution=False)

# @given(_strategy_NaiveFunction_FV3())
# def test_SymbolicVectorRelation_Nearlattice_law_initialSegment_isA_BoundedLattice_forAll(f: NaiveFunction[F3, Bplus], ps: Set[NaiveFunction[F3, Bplus]]):
#   assert check_consistency_oneMany( eq, f, ps, f_is_unique_solution=False, addFinalNullPSArg=False)

# OverridingNearlattice

#is_override(a, left, right, ps)
#law_override_exists_forAll(left, right, ps)

# BooleanNearlattice

# law_initialSegment_isA_ComplementedLattice_forAll(a, ps)
# law_initialSegment_isA_DistributiveLattice_forAll(a, x, y, z, ps)

# TODO - test consistency for typeclass instances of SymbolicArrayFunction
