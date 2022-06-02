import typing
from typing import get_args#, overload, TypeVar
from typing import Optional, Union#, Collection, Sequence
from typing import Collection, Sequence, Tuple, List, Set, FrozenSet
from classes import AssociatedType, Supports, typeclass


from funcy import lmap
from functools import reduce

import hypothesis
from hypothesis import given, strategies as st
import pytest

import z3

import saguaro.utilities as SU
from saguaro.utilities import foldl, A
import saguaro._Boolean as SB
# import saguaro.Eq as Eq
# import saguaro.Order as Ord
# import saguaro.FiniteSubset as FS
# import saguaro.FeatureVector as FV
# import saguaro.ConcreteTrits as ct
# import saguaro.SymbolicBools as sb
# import saguaro.FiniteSubset as fs


# st.register_type_strategy(custom_type, strategy)


# BASIC TESTS

def test_should_pass():
  assert False == False

# def test_should_fail():
#   assert False == True


# CONCRETE SUBSETS AND SUBSET VECTORS

O3 = ["a", "b", "c"]
PO3 = [ []
      , ["a"]
      , ["b"]
      , ["c"]
      , ["a", "b"]
      , ["a", "c"]
      , ["b", "c"]
      , ["a", "b", "c"]
      ]
SV3 = [ [False, False, False] #0
      , [True , False, False] #1
      , [False, True , False] #2
      , [False, False, True ] #3
      , [True , True , False] #4
      , [True , False, True ] #5
      , [False, True , True ] #6
      , [True , True , True ] #7
      ]

# FiniteSubset:
# - low priority tests
#   - allSubsetVectors
#   - mk_subset_fromSubsetVector
#   - mk_subsetVector_fromSubset
#   - isSubsetEq #subsetvectors
#   - orphaned test

# def test_subset():
#   for ss, v in zip(PO3, SV3):
#     assert ss == u.mk_subset_fromSubsetVector(list)(O3)(v), f"{ss}, {v}, {u.mk_subset_fromSubsetVector(list)(O3)(v)}"
#     assert v  == u.mk_subsetVector_fromSubset(list)(O3)(ss), f"{ss}, {v}, {u.mk_subsetVector_fromSubset(list)(O3)(ss)}"
#     assert u.isSubsetEq(SV3[0], v0), f"{SV3[0]}, {v0}"

#   assert not u.isSubSetEq(SV3[1], SV3[0])
#   assert u.isSubSetEq(SV3[1], SV3[1])
#   assert not u.isSubSetEq(SV3[1], SV3[2])
#   assert not u.isSubSetEq(SV3[1], SV3[3])
#   assert u.isSubSetEq(SV3[1], SV3[4])
#   assert u.isSubSetEq(SV3[1], SV3[5])
#   assert not u.isSubSetEq(SV3[1], SV3[6])
#   assert u.isSubSetEq(SV3[1], SV3[7])

#   assert not u.isSubSetEq(SV3[4], SV3[0])
#   assert not u.isSubSetEq(SV3[4], SV3[1])
#   assert not u.isSubSetEq(SV3[4], SV3[2])
#   assert not u.isSubSetEq(SV3[4], SV3[3])
#   assert u.isSubSetEq(SV3[4], SV3[4])
#   assert not u.isSubSetEq(SV3[4], SV3[5])
#   assert not u.isSubSetEq(SV3[4], SV3[6])
#   assert u.isSubSetEq(SV3[4], SV3[7])
