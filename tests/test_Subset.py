# from typing import get_args#, overload, TypeVar
from typing import Optional, Union, Callable#, Collection, Sequence
from typing import Collection, Sequence, Tuple, List, Set, FrozenSet
# from classes import AssociatedType, Supports, typeclass

import hypothesis
from hypothesis import given, settings
from hypothesis import strategies as st
from hypothesis.strategies import SearchStrategy

from funcy import lmap, lmapcat

import z3

import saguaro.utilities as SU
import saguaro._Boolean as SB
import saguaro.Eq as SE
import saguaro.Order as SO
import saguaro.Subset as SS

NS = SS.NaiveSubset
SVS = SS.SymbolicVectorSubset

from saguaro.utilities import A, getModel, fst, snd
from saguaro._Boolean import Bool, Constraint, Constraints \
                           , id_Bool \
                           , bool_to_BoolRef1
from saguaro._Boolean import Not, Not1 \
                           , And, And1 \
                           , Or, Or1 \
                           , Implies, Implies1 \
                           , Iff, Iff1 \
                           , _strategy_bool, _strategy_BoolRef
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
from saguaro.Subset import Subset, NaiveSubset, SymbolicVectorSubset
from saguaro.Subset import is_empty, is_nonempty, has_element, missing_element, \
                           is_difference, is_union, is_intersection, \
                           is_subseteq, is_supseteq
from saguaro.Subset import _strategy_NaiveSubset_int, \
                           _strategy_NaiveSubset_PS_int, \
                           _strategy_NaiveSubset_Set_int
# from saguaro.Subset import _strategy_NaiveSubset_PS_bot_int
# from saguaro.Subset import _strategy_NaiveSubset_PS_top_int


def test_should_pass():
  assert False == False

# def test_should_fail():
#   assert False == True

############################
# TESTS AGAINST FIXED DATA #
############################

u2             = set([1, 2])
u3             = set([1, 2, 3])
zero: set[int] = set()
one            = set([1])
two            = set([2])
three          = set([3])
oneTwo         = set([1, 2])
oneThree       = set([1, 3])
twoThree       = set([2, 3])
oneTwoThree    = set([1, 2, 3])

u2_ns          = NS(u2, u2)
u3_ns          = NS(u3, u3)
zero_ns        = NS(zero, u3)
one_ns         = NS(one, u3)
two_ns         = NS(two, u3)
three_ns       = NS(three, u3)
oneTwo_ns      = NS(oneTwo, u3)
oneThree_ns    = NS(oneThree, u3)
twoThree_ns    = NS(twoThree, u3)
oneTwoThree_ns = NS(oneTwoThree, u3)

u3_ps = set([ zero_ns
            , one_ns, two_ns, three_ns
            , oneTwo_ns, oneThree_ns, twoThree_ns
            , oneTwoThree_ns
            ])

# Main goal of "basic" tests is simply to check that every call of
# every type signature expected is defined and has the expected type

def test_NaiveSubset_implementation_basic_construction():
  assert type(u2_ns) == NS
  assert type(u3_ns) == NS
  assert type(zero_ns) == NS
  assert type(one_ns) == NS
  assert type(oneTwo_ns) == NS
  assert type(twoThree_ns) == NS

def test_NaiveSubset_implementation_basic_collectionMethods():
  assert len(oneTwo_ns) == 2
  assert 1 in oneTwo_ns
  assert 0 not in oneTwo_ns

def test_NaiveSubset_implementation_basic_consistencyAndEqualityMethods():
  assert NS.same_universe(u3_ns, one_ns)
  assert NS.same_universes({u3_ns, one_ns, oneTwo_ns})
  assert NS.same_subsets({oneTwo_ns, oneTwo_ns})
  assert NS.same_subset(NS._difference_NaiveSubset(u3_ns, twoThree_ns), one_ns)

def test_NaiveSubset_implementation_basic_equality():
  assert eq(NS._difference_NaiveSubset(u3_ns, twoThree_ns), one_ns)
  assert eq1([oneTwo_ns, oneTwo_ns])
  assert neq(oneTwo_ns, one_ns)
  assert neq(u2_ns, u3_ns)
  assert neq1([oneTwo_ns, one_ns])

def test_NaiveSubset_implementation_basic_enumerate_Preorder():
  assert _enumerate_Preorder(one_ns) == _enumerate_Preorder(oneTwo_ns)
  print(_enumerate_Preorder(one_ns))
  assert _enumerate_Preorder(one_ns) == _ConcreteEnumeration.freeze(
                                          { zero_ns
                                          , one_ns, two_ns, three_ns
                                          , oneTwo_ns, oneThree_ns, twoThree_ns
                                          , oneTwoThree_ns
                                          }
                                        )

def test_NaiveSubset_implementation_basic_enumerate_atoms_from_universe():
  assert NS._enumerate_atoms_from_universe(u3) == {one_ns, two_ns, three_ns}

def test_NaiveSubset_implementation_basic_enumerate_universe_from_atoms():
  assert NS._enumerate_universe_from_atoms({one_ns, two_ns, three_ns}) ==  u3

def test_NaiveSubset_implementation_basic_comparison():
  assert le(one_ns, oneTwo_ns)
  assert lt(one_ns, oneTwo_ns)
  assert not ge(one_ns, oneTwo_ns)
  assert not gt(one_ns, oneTwo_ns)

def test_NaiveSubset_implementation_basic_semilatticeOpsAsFunctions():
  assert NS._meet_NaiveSubset(one_ns, oneTwo_ns) == one_ns
  assert NS._join_NaiveSubset(one_ns, oneTwo_ns) == oneTwo_ns
  assert NS._meet1_NaiveSubset({one_ns, oneTwo_ns}) == one_ns
  assert NS._join1_NaiveSubset({one_ns, oneTwo_ns}) == oneTwo_ns

def test_NaiveSubset_implementation_basic_semilatticeOpsAsRelations():
  assert is_least_upper_bound(oneTwo_ns, one_ns, oneTwo_ns, u3_ps)
  assert is_greatest_lower_bound(one_ns, one_ns, oneTwo_ns, u3_ps)
  assert is_least_upper_bound1(oneTwo_ns, {one_ns, oneTwo_ns}, u3_ps)
  assert is_greatest_lower_bound1(one_ns, {one_ns, oneTwo_ns}, u3_ps)

def test_NaiveSubset_implementation_basic_setOpsAsFunctions():
  assert eq(NS._union_NaiveSubset(one_ns, twoThree_ns), u3_ns)
  assert eq(NS._intersection_NaiveSubset(one_ns, twoThree_ns), zero_ns)
  assert eq1({NS._union_NaiveSubset(one_ns, twoThree_ns), u3_ns})
  assert eq1({NS._intersection_NaiveSubset(one_ns, twoThree_ns), zero_ns})

  assert complementary(one_ns, twoThree_ns, u3_ps)

  assert is_empty(zero_ns)
  assert is_nonempty(one_ns)
  assert is_nonempty(oneTwo_ns)
  assert is_nonempty(u3_ns)
  assert has_element(oneTwoThree_ns, 3)
  assert missing_element(twoThree_ns, 1)
  assert is_subseteq(oneTwoThree_ns, u3_ns)
  assert le(oneTwoThree_ns, u3_ns)
  assert not is_supseteq(oneTwo_ns, u3_ns)

  # default implementations in `Order`
def test_NaiveSubset_implementation_basic_defaultImplementations():
  assert comparable(zero_ns, oneThree_ns)
  assert comparable(one_ns, oneThree_ns)
  assert not comparable(one_ns, twoThree_ns)
  assert is_between(one_ns, zero_ns, oneTwo_ns)
  assert is_in_interval(one_ns, zero_ns, oneTwo_ns)

  assert is_minimal(one_ns    , {one_ns, oneTwo_ns})
  assert is_maximal(oneTwo_ns , {one_ns, oneTwo_ns})
  assert is_least(one_ns      , {one_ns, oneTwo_ns})
  assert is_greatest(oneTwo_ns, {one_ns, oneTwo_ns})
  assert is_lower_bound(zero_ns, {two_ns})
  assert is_upper_bound(two_ns, {zero_ns})
  assert is_global_lower_bound(zero_ns, u3_ps)
  assert is_global_upper_bound(u3_ns, u3_ps)

# The tests below are more systematic - though they could be made more thorough.

def test_NaiveSubset_implementation_bot():
  for each in u3_ps:
    assert global_lower_bound(each, None) == zero_ns

def test_NaiveSubset_implementation_top():
  for each in u3_ps:
    assert global_upper_bound(each, None) == oneTwoThree_ns

def test_NaiveSubset_implementation_is_meet1():
  assert is_meet1(one_ns        , {one_ns        , oneTwo_ns     , oneThree_ns, oneTwoThree_ns}, u3_ps)
  for each in filter(lambda each: each is not one_ns, u3_ps):
    assert not is_meet1(each    , {one_ns        , oneTwo_ns     , oneThree_ns, oneTwoThree_ns}, u3_ps), f"{each}"
  assert is_meet1(two_ns        , {two_ns        , oneTwo_ns     , twoThree_ns, oneTwoThree_ns}, u3_ps)
  for each in filter(lambda each: each is not two_ns, u3_ps):
    assert not is_meet1(each    , {two_ns        , oneTwo_ns     , twoThree_ns, oneTwoThree_ns}, u3_ps), f"{each}"
  assert is_meet1(three_ns      , {three_ns      , oneThree_ns   , twoThree_ns, oneTwoThree_ns}, u3_ps)
  for each in filter(lambda each: each is not three_ns, u3_ps):
    assert not is_meet1(each    , {three_ns      , oneThree_ns   , twoThree_ns, oneTwoThree_ns}, u3_ps), f"{each}"
  assert is_meet1(oneTwo_ns     , {oneTwo_ns     , oneTwoThree_ns}, u3_ps)
  for each in filter(lambda each: each is not oneTwo_ns, u3_ps):
    assert not is_meet1(each    , {oneTwo_ns     , oneTwoThree_ns}, u3_ps), f"{each}"
  assert is_meet1(oneThree_ns   , {oneThree_ns   , oneTwoThree_ns}, u3_ps)
  for each in filter(lambda each: each is not oneThree_ns, u3_ps):
    assert not is_meet1(each    , {oneThree_ns   , oneTwoThree_ns}, u3_ps), f"{each}"
  assert is_meet1(twoThree_ns   , {twoThree_ns   , oneTwoThree_ns}, u3_ps)
  for each in filter(lambda each: each is not twoThree_ns, u3_ps):
    assert not is_meet1(each    , {twoThree_ns   , oneTwoThree_ns}, u3_ps), f"{each}"
  assert is_meet1(oneTwoThree_ns, {oneTwoThree_ns}, u3_ps)
  for each in filter(lambda each: each is not oneTwoThree_ns, u3_ps):
    assert not is_meet1(each    , {oneTwoThree_ns}, u3_ps), f"{each}"

def test_NaiveSubset_implementation_is_join1():
  assert is_join1(one_ns        , {one_ns  , zero_ns}, u3_ps)
  for each in filter(lambda each: each is not one_ns, u3_ps):
    assert not is_join1(each    , {one_ns  , zero_ns}, u3_ps), f"{each}"
  assert is_join1(two_ns        , {two_ns  , zero_ns}, u3_ps)
  for each in filter(lambda each: each is not two_ns, u3_ps):
    assert not is_join1(each    , {two_ns  , zero_ns}, u3_ps), f"{each}"
  assert is_join1(three_ns      , {three_ns, zero_ns}, u3_ps)
  for each in filter(lambda each: each is not three_ns, u3_ps):
    assert not is_join1(each    , {three_ns, zero_ns}, u3_ps), f"{each}"
  assert is_join1(oneTwo_ns     , {one_ns  , two_ns}, u3_ps)
  for each in filter(lambda each: each is not oneTwo_ns, u3_ps):
    assert not is_join1(each    , {one_ns  , two_ns}, u3_ps), f"{each}"
  assert is_join1(oneThree_ns   , {one_ns  , three_ns}, u3_ps)
  for each in filter(lambda each: each is not oneThree_ns, u3_ps):
    assert not is_join1(each    , {one_ns  , three_ns}, u3_ps), f"{each}"
  assert is_join1(twoThree_ns   , {two_ns  , three_ns}, u3_ps)
  for each in filter(lambda each: each is not twoThree_ns, u3_ps):
    assert not is_join1(each    , {two_ns  , three_ns}, u3_ps), f"{each}"
  assert is_join1(oneTwoThree_ns, {one_ns  , two_ns  , three_ns}, u3_ps)
  for each in filter(lambda each: each is not oneTwoThree_ns, u3_ps):
    assert not is_join1(each    , {one_ns  , two_ns  , three_ns}, u3_ps), f"{each}"

def test_NaiveSubset_implementation_has_meet1():
  assert has_meet1({one_ns        , oneTwo_ns     , oneThree_ns, oneTwoThree_ns}, u3_ps)
  assert has_meet1({two_ns        , oneTwo_ns     , twoThree_ns, oneTwoThree_ns}, u3_ps)
  assert has_meet1({three_ns      , oneThree_ns   , twoThree_ns, oneTwoThree_ns}, u3_ps)
  assert has_meet1({oneTwo_ns     , oneTwoThree_ns}, u3_ps)
  assert has_meet1({oneThree_ns   , oneTwoThree_ns}, u3_ps)
  assert has_meet1({twoThree_ns   , oneTwoThree_ns}, u3_ps)
  assert has_meet1({oneTwoThree_ns}, u3_ps)

def test_NaiveSubset_implementation_has_join1():
  assert has_join1({one_ns  , zero_ns}, u3_ps)
  assert has_join1({two_ns  , zero_ns}, u3_ps)
  assert has_join1({three_ns, zero_ns}, u3_ps)
  assert has_join1({one_ns  , two_ns}, u3_ps)
  assert has_join1({one_ns  , three_ns}, u3_ps)
  assert has_join1({two_ns  , three_ns}, u3_ps)
  assert has_join1({one_ns  , two_ns  , three_ns}, u3_ps)

def test_NaiveSubset_implementation_is_difference():
  assert is_difference(one_ns     , oneTwo_ns  , two_ns)
  assert is_difference(one_ns     , oneThree_ns, three_ns)
  assert is_difference(twoThree_ns, twoThree_ns, one_ns)
  assert is_difference(zero_ns    , oneTwo_ns  , oneTwo_ns)
  assert is_difference(u3_ns      , u3_ns      , zero_ns)
  assert is_difference(oneTwo_ns  , oneTwo_ns  , zero_ns)

def test_NaiveSubset_implementation_complementary():
  assert complementary(one_ns, twoThree_ns, u3_ps)
  assert complementary(two_ns, oneThree_ns, u3_ps)
  assert complementary(three_ns, oneTwo_ns, u3_ps)
  assert complementary(zero_ns, oneTwoThree_ns, u3_ps)
  assert complementary(twoThree_ns, one_ns, u3_ps)
  assert complementary(oneThree_ns, two_ns, u3_ps)
  assert complementary(oneTwo_ns, three_ns, u3_ps)
  assert complementary(oneTwoThree_ns, zero_ns, u3_ps)

def test_NaiveSubset_implementation_covers():
  assert covers(one_ns, zero_ns, u3_ps)
  assert covers(two_ns, zero_ns, u3_ps)
  assert covers(three_ns, zero_ns, u3_ps)
  assert not covers(zero_ns, one_ns, u3_ps)
  assert not covers(zero_ns, two_ns, u3_ps)
  assert not covers(zero_ns, three_ns, u3_ps)
  assert covers(oneTwo_ns, one_ns, u3_ps)
  assert not covers(oneTwo_ns, zero_ns, u3_ps)
  assert covers(oneTwoThree_ns, twoThree_ns, u3_ps)
  assert not covers(oneTwoThree_ns, zero_ns, u3_ps)

def test_NaiveSubset_implementation_is_chain():
  assert is_chain({zero_ns, one_ns})
  assert is_chain({zero_ns, two_ns})
  assert is_chain({zero_ns, oneThree_ns})
  assert not is_chain({zero_ns, one_ns, two_ns})
  assert is_chain({zero_ns, one_ns, oneTwo_ns, oneTwoThree_ns})

def test_NaiveSubset_implementation_is_atom():
  assert is_atom(one_ns, u3_ps)
  assert is_atom(two_ns, u3_ps)
  assert is_atom(three_ns, u3_ps)
  assert is_atom1({one_ns, two_ns, three_ns}, u3_ps)
  assert is_atom1({two_ns, three_ns}, u3_ps)
  assert not is_atom(zero_ns, u3_ps)
  assert not is_atom(oneThree_ns, u3_ps)
  assert not is_atom(oneTwoThree_ns, u3_ps)


##########################
# PROPERTY-BASED TESTING #
##########################

#########################################
# Order-theoretic structure law testing #
#########################################

# NB NaiveSubset[A] is a *parametrically polymorphic type*, just like List[A]
# or Set[A]:
#  - it has a single implementation that is invariant across all possible A
#    types.
# Accordingly, the tests below use NaiveSubset[int] rather than
# NaiveSubset[<whatever>] for no particular reason other than that at least one
# type needs a `hypothesis` strategy for property-based testing.

# Eq laws

@given(_strategy_NaiveSubset_int())
def test_Eq_law_reflexivity_NaiveSubset_int(s: NaiveSubset[int]):
  assert SE.law_reflexivity_forAll(s)

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_Eq_law_symmetry_NaiveSubset_int(a: NaiveSubset[int], b: NaiveSubset[int]):
  assert SE.law_symmetry_forAll(a, b)

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_Eq_law_transitivity_NaiveSubset_int(a: NaiveSubset[int], b: NaiveSubset[int], c: NaiveSubset[int]):
  assert SE.law_transitivity_forAll(a, b, c)


# Preorder laws
@given(_strategy_NaiveSubset_int())
def test_Preorder_law_reflexivity_NaiveSubset_int(s: NaiveSubset[int]):
  assert SO.law_reflexivity_forAll(s)

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_Preorder_law_transitivity_NaiveSubset_int(a: NaiveSubset[int], b: NaiveSubset[int], c: NaiveSubset[int]):
  assert SO.law_transitivity_forAll(a, b, c)

# LowerBounded laws
@given(_strategy_NaiveSubset_PS_int())
def test_LowerBounded_law_lowerBounded_NaiveSubset_int(ps: Collection[NaiveSubset[int]]):
  assert law_lowerBounded(ps)

# UpperBounded laws
@given(_strategy_NaiveSubset_PS_int())
def test_UpperBounded_law_upperBounded_NaiveSubset_int(ps: Collection[NaiveSubset[int]]):
  assert law_upperBounded(ps)

# PartialOrder laws
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_PartialOrder_law_antisymmetric_NaiveSubset_int(a: NaiveSubset[int], b: NaiveSubset[int]):
  assert law_antisymmetric_forAll(a, b)

# MeetSemilattice laws
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_PS_int())
def test_MeetSemilattice_law_meetExists_NaiveSubset_int(a: NaiveSubset[int], b: NaiveSubset[int], ps: Set[NaiveSubset[int]]):
  assert law_meetExists_forAll(a, b, ps)

# JoinSemilattice laws
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_PS_int())
def test_JoinSemilattice_law_joinExists_NaiveSubset_int(a: NaiveSubset[int], b: NaiveSubset[int], ps: Set[NaiveSubset[int]]):
  assert law_joinExists_forAll(a, b, ps)

# ComplementedLattice laws
@settings(deadline=22000)
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_PS_int())
def test_ComplementedLattice_law_complementExists_NaiveSubset_int(a: NaiveSubset[int], ps: Set[NaiveSubset[A]]):
  assert law_complementExists_forAll(a, ps)

# # DistributiveLattice laws
@settings(deadline=20000)
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_PS_int())
def test_DistributiveLattice_law_meetDistributesOverJoin_NaiveSubset_int(x: NaiveSubset[int], y: NaiveSubset[int], z: NaiveSubset[int], ps: Collection[NaiveSubset[int]]):
  assert law_meetDistributesOverJoin_forAll(x, y, z, ps)



############################################################################
# Testing consistency between symbolic and concrete subset implementations #
############################################################################


def check_SymbolicVectorSubset_conversion(value: NaiveSubset[int]):
  value_symbolic, constraint = SymbolicVectorSubset.mk_from_NaiveSubset("value", tuple(sorted(value.universe)), value)

  model, _ = getModel([constraint])

  if model is not None:
    value_concrete = value_symbolic.to_NaiveSubset(model)
    assert eq(value_concrete, value)
  else:
    raise Exception(f"No model found while trying to roundtrip {value}")
  return True

# TODO - add roundtrip test for SymbolicArraySubset

# The general strategy to test a relation
#   r : Subset x Subset x Subset x Set[Subset] -> Bool)
#   r(subset, left, right, subsets)
# is to generate (usually random) example inputs for each of the arguments
# (via `hypothesis` search strategies), and to then use z3 to check the *first*
# argument while holding the others fixed.

# For now, there are as many `check_consistency_<...>` as there are patterns
# of arguments to check.
# This is a solveable problem of redundancy, but for now things are simple and
# 'unspooled'.
# TODO - consolidate the `check_consistency` functions
# TODO - figure out if there's an easy way to not have to rewrite all of this
# for use with `SymbolicArraySubset`

def check_consistency_one( f: Callable[[Subset], Bool]
                           , subset: NaiveSubset[A]
                           , subset_is_unique_solution: bool = True
                           , addFinalNullPSArg: bool = False
                          ):
  if addFinalNullPSArg:
    g = lambda subset: f(subset, None)  # type: ignore
  else:
    g = f
  concrete_result = g(subset)

  u = tuple(sorted(subset.universe))  # type: ignore

  if concrete_result:

    # Construct a fresh symbolic subset that we (usually) want to end up being
    # identical to the concrete `subset` passed in as an argument
    fresh_symbolic_subset = SymbolicVectorSubset.mk("fresh", u)

    # Construct a constraint indicating that `fresh_symbolic_subset` satisfies
    # the relation `f` wrt `subsets_symbolic`.
    symbolic_constraint: Constraint = g(fresh_symbolic_subset)

    # Task z3 with finding a model with all relevant constraints
    constraints = [symbolic_constraint]
    model, _    = getModel(constraints)

    if model is not None: # the solver has found a solution for `fresh_symbolic_subset`
      concretized_symbolic_solution = fresh_symbolic_subset.to_NaiveSubset(model)

      # we're expecting a solution (viz. one equal to `subset`)
      if eq(subset, concretized_symbolic_solution):
        return True
      elif subset_is_unique_solution: # the synthesized solution is not what we're expecting
        raise Exception(f"Solver produced unexpected alternative.\nExpected: '{subset}'\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{subset}\n{constraints}")
      else:
        # check whether `subset` is a possible solution, according to the symbolic implementation
        symbolicized_concrete_solution, scs_constraint = SymbolicVectorSubset.mk_from_NaiveSubset("concrete_subset", u, subset)
        freshSubset_eq_subset_constraint: Constraint = eq(fresh_symbolic_subset, symbolicized_concrete_solution)
        model, _ = getModel(constraints + [scs_constraint] + [freshSubset_eq_subset_constraint])

        if model is not None: # we've verified that the symbolic model accepts `subset` as a solution
          concretized_symbolic_solution_alt = fresh_symbolic_subset.to_NaiveSubset(model)
          assert eq(concretized_symbolic_solution_alt, subset), f"{subset} vs. {concretized_symbolic_solution_alt}" # lots of things have gone wrong if this assertion ever fails
          return True
        else: # solver has not found a solution under the constraints we've imposed
          raise Exception(f"Solver produced unexpected alternative and does not agree with concrete implementation.\nExpected: '{subset}'\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{subset}\n{constraints}")
    else: # there is no synthesized solution where we expected one
      raise Exception(f"Unexpected lack of solution from solver.\nExpected: '{subset}'\nbut got: nothing\nfrom:\n{f}\n{subset}\n{constraints}")
  else:
    # Construct a symbolic subset that is equal to `subset`
    symbolic_subset, subset_constraint = SymbolicVectorSubset.mk_from_NaiveSubset("subset", u, subset)

    # Construct a constraint indicating that `symbolic_subset` satisfies the `f`
    # relation wrt `subsets_symbolic`
    symbolic_constraint: Constraint = g(symbolic_subset)  # type: ignore

    # Ask z3 to find a model with all relevant constraints
    constraints = [symbolic_constraint] + [subset_constraint]
    model, _    = getModel(constraints)

    if model is not None: # the solver thinks `subset` is actually a solution
      concretized_symbolic_solution = symbolic_subset.to_NaiveSubset(model)
      assert eq(concretized_symbolic_solution, subset), f"{subset} vs. {concretized_symbolic_solution}" # lots of things have gone wrong if this assertion ever fails
      raise Exception(f"Symbolic implementation thinks `subset` is a solution where concrete implementation does NOT.\nExpected: no solution\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{subset}\n{constraints}")
    else: # no solution found, as expected
      return True

def check_consistency_oneMany( f: Callable[[Subset, Collection[Subset]], Bool]
                             , subset: NaiveSubset[A]
                             , subsets: Set[NaiveSubset[A]]
                             , subset_is_unique_solution: bool = True
                             , addFinalNullPSArg: bool = False
                             ):
  """
  Check for consistency between the concrete and symbolic implementations of `f`
  on specific arguments.

  Given
    - a typeclass relation f(subset: Subset, subsets: Set[Subset]) -> Bool
    - two concrete arguments `subset` and `subsets`
      - Note that NO assumption is made that f(subset, subsets) == True or False.
    - a flag value indicating whether `subset` is expected to be a unique
      solution of the relation (holding `subsets`) fixed...

  ...this function uses z3 to try to synthesize a value for `subset` (while
  holding `subsets` fixed).

  If `f(subset, subsets) == True`, this uses the symbolic version of `f` and
  `subsets` to synthesize a solution to `f(???, subsets)` and checks that
  the solution is the same as `subset`. (If the boolean flag argument indicates
  that `subset` is not a unique solution, the function checks that `subset` is
  a solution.)

  If `f(subset, subsets) == False`, this uses symbolic versions of `f`,
  `subset`, and `subsets` and attempts to show that there is no model where
  `f(subset, subsets)` holds.
  """
  # Calculate the result of f on both concrete arguments
  if addFinalNullPSArg:
    g = lambda subset, subsets: f(subset, subsets, None)  # type: ignore
  else:
    g = f

  concrete_result = g( subset
                     , subsets
                     )

  # Construct symbolic versions of the collection argument (`subsets`)
  u = tuple(sorted(subset.universe))  # type: ignore
  def _mk(identifier: str, ns: NaiveSubset[A]) -> Tuple[SymbolicVectorSubset[A], Constraint]:
    return SymbolicVectorSubset.mk_from_NaiveSubset(identifier, u, ns)
  subsets_plus_constraints = [ _mk(f"set_{i}", s)
                               for i,s in enumerate(subsets)
                             ]
  subsets_symbolic: List[SymbolicVectorSubset[A]] = lmap(fst, subsets_plus_constraints)
  subsets_constraints: List[Constraint]           = lmap(snd, subsets_plus_constraints)

  if concrete_result:

    # Construct a fresh symbolic subset that we (usually) want to end up being
    # identical to the concrete `subset` passed in as an argument
    fresh_symbolic_subset = SymbolicVectorSubset.mk("fresh", u)

    # Construct a constraint indicating that `fresh_symbolic_subset` satisfies
    # the relation `f` wrt `subsets_symbolic`.
    symbolic_constraint: Constraint = g( fresh_symbolic_subset
                                       , set(subsets_symbolic)
                                       )

    # Task z3 with finding a model with all relevant constraints
    constraints = [symbolic_constraint] + subsets_constraints
    model, _    = getModel(constraints)

    if model is not None: # the solver has found a solution for `fresh_symbolic_subset`
      concretized_symbolic_solution = fresh_symbolic_subset.to_NaiveSubset(model)

      # we're expecting a solution (viz. one equal to `subset`)
      if eq(subset, concretized_symbolic_solution):
        return True
      elif subset_is_unique_solution: # the synthesized solution is not what we're expecting
        raise Exception(f"Solver produced unexpected alternative.\nExpected: '{subset}'\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{subset}\n{subsets}\n{constraints}")
      else:
        # check whether `subset` is a possible solution, according to the symbolic implementation
        symbolicized_concrete_solution, scs_constraint = SymbolicVectorSubset.mk_from_NaiveSubset("concrete_subset", u, subset)
        freshSubset_eq_subset_constraint: Constraint = eq(fresh_symbolic_subset, symbolicized_concrete_solution)
        model, _ = getModel(constraints + [scs_constraint] + [freshSubset_eq_subset_constraint])

        if model is not None: # we've verified that the symbolic model accepts `subset` as a solution
          concretized_symbolic_solution_alt = fresh_symbolic_subset.to_NaiveSubset(model)
          assert eq(concretized_symbolic_solution_alt, subset), f"{subset} vs. {concretized_symbolic_solution_alt}" # lots of things have gone wrong if this assertion ever fails
          return True
        else: # solver has not found a solution under the constraints we've imposed
          raise Exception(f"Solver produced unexpected alternative and does not agree with concrete implementation.\nExpected: '{subset}'\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{subset}\n{subsets}\n{constraints}")
    else: # there is no synthesized solution where we expected one
      raise Exception(f"Unexpected lack of solution from solver.\nExpected: '{subset}'\nbut got: nothing\nfrom:\n{f}\n{subset}\n{subsets}\n{constraints}")
  else:
    # Construct a symbolic subset that is equal to `subset`
    symbolic_subset, subset_constraint = SymbolicVectorSubset.mk_from_NaiveSubset("subset", u, subset)

    # Construct a constraint indicating that `symbolic_subset` satisfies the `f`
    # relation wrt `subsets_symbolic`
    symbolic_constraint: Constraint = g( symbolic_subset  # type: ignore
                                       , set(subsets_symbolic)
                                       )

    # Ask z3 to find a model with all relevant constraints
    constraints = [symbolic_constraint] + subsets_constraints + [subset_constraint]
    model, _    = getModel(constraints)

    if model is not None: # the solver thinks `subset` is actually a solution
      concretized_symbolic_solution = symbolic_subset.to_NaiveSubset(model)
      assert eq(concretized_symbolic_solution, subset), f"{subset} vs. {concretized_symbolic_solution}" # lots of things have gone wrong if this assertion ever fails
      raise Exception(f"Symbolic implementation thinks `subset` is a solution where concrete implementation does NOT.\nExpected: no solution\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{subset}\n{subsets}\n{constraints}")
    else: # no solution found, as expected
      return True

def check_consistency_oneOne( f: Callable[[Subset, Subset], Bool]
                            , left: NaiveSubset[A]
                            , right: NaiveSubset[A]
                            , left_is_unique_solution: bool = True
                            # , addFinalNullPSArg: bool = False
                            ):
  # if addFinalNullPSArg:
    # raise NotImplementedError("")

  concrete_result = f( left
                     , right
                     )

  u = tuple(sorted(left.universe))  # type: ignore
  right_symbolic, right_constraint = SymbolicVectorSubset.mk_from_NaiveSubset( f"concrete_right"
                                                                             , u
                                                                             , right
                                                                             )
  if concrete_result:

    fresh_symbolic_subset = SymbolicVectorSubset.mk("fresh", u)
    symbolic_constraint: Constraint = f( fresh_symbolic_subset
                                       , right_symbolic
                                       )

    constraints = [symbolic_constraint] + [right_constraint]
    model, _    = getModel(constraints)

    if model is not None:
      concretized_symbolic_solution = fresh_symbolic_subset.to_NaiveSubset(model)

      if eq(left, concretized_symbolic_solution):
        return True
      elif left_is_unique_solution:
        raise Exception(f"Solver produced unexpected alternative.\nExpected: '{left}'\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{left}\n{right}\n{constraints}")
      else:
        symbolicized_concrete_solution, scs_constraint = SymbolicVectorSubset.mk_from_NaiveSubset("concrete_left", u, left)
        freshSubset_eq_left_constraint: Constraint = eq(fresh_symbolic_subset, symbolicized_concrete_solution)
        model, _ = getModel(constraints + [scs_constraint] + [freshSubset_eq_left_constraint])

        if model is not None:
          concretized_symbolic_solution_alt = fresh_symbolic_subset.to_NaiveSubset(model)
          assert eq(concretized_symbolic_solution_alt, left), f"{left} vs. {concretized_symbolic_solution_alt}"  # lots of things have gone wrong if this assertion ever fails
          return True
        else:
          raise Exception(f"Solver produced unexpected alternative and does not agree with concrete implementation.\nExpected: '{left}'\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{left}\n{right}\n{constraints}")
    else:
      raise Exception(f"Unexpected lack of solution from solver.\nExpected: '{left}'\nbut got: nothing\nfrom:\n{f}\n{left}\n{right}\n{constraints}")
  else:
    symbolic_left, left_constraint = SymbolicVectorSubset.mk_from_NaiveSubset(f"concrete_left", u, left)

    symbolic_constraint: Constraint = f( symbolic_left  # type: ignore
                                       , right_symbolic
                                       )

    constraints = [symbolic_constraint] + [right_constraint] + [left_constraint]
    model, _    = getModel(constraints)

    if model is not None:
      concretized_symbolic_solution = symbolic_left.to_NaiveSubset(model)
      assert eq(concretized_symbolic_solution, left), f"{left} vs. {concretized_symbolic_solution}"  # lots of things have gone wrong if this assertion ever fails
      raise Exception(f"Symbolic implementation thinks `left` is a solution where concrete implementation does NOT.\nExpected: no solution\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{left}\n{right}\n{constraints}")
    else:
      return True

def check_consistency_oneOneMany( f: Callable[[Subset, Subset, Collection[Subset]], Bool]
                                , left: NaiveSubset[A]
                                , right: NaiveSubset[A]
                                , subsets: Set[NaiveSubset[A]]
                                , left_is_unique_solution: bool = True
                                # , addFinalNullPSArg: bool = False
                                ):
  # if addFinalNullPSArg:
    # raise NotImplementedError("")

  concrete_result = f( left
                     , right
                     , subsets
                     )
  u = tuple(sorted(left.universe))  # type: ignore
  right_symbolic, right_constraint = SymbolicVectorSubset.mk_from_NaiveSubset( f"concrete_right"
                                                                             , u
                                                                             , right
                                                                             )
  def _mk(identifier: str, ns: NaiveSubset[A]) -> Tuple[SymbolicVectorSubset[A], Constraint]:
    return SymbolicVectorSubset.mk_from_NaiveSubset(identifier, u, ns)
  subsets_plus_constraints = [ _mk(f"set_{i}", s)
                               for i,s in enumerate(subsets)
                             ]
  subsets_symbolic: List[SymbolicVectorSubset[A]] = lmap(fst, subsets_plus_constraints)
  subsets_constraints: List[Constraint]           = lmap(snd, subsets_plus_constraints)

  if concrete_result:

    fresh_symbolic_subset = SymbolicVectorSubset.mk("fresh", u)
    symbolic_constraint: Constraint = f( fresh_symbolic_subset
                                       , right_symbolic
                                       , set(subsets_symbolic)
                                       )

    constraints = [symbolic_constraint] + [right_constraint] + subsets_constraints
    model, _    = getModel(constraints)

    if model is not None:
      concretized_symbolic_solution = fresh_symbolic_subset.to_NaiveSubset(model)

      if eq(left, concretized_symbolic_solution):
        return True
      elif left_is_unique_solution:
        raise Exception(f"Solver produced unexpected alternative.\nExpected: '{left}'\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{left}\n{right}\n{subsets}\n{constraints}")
      else:
        symbolicized_concrete_solution, scs_constraint = SymbolicVectorSubset.mk_from_NaiveSubset("concrete_left", u, left)
        freshSubset_eq_left_constraint: Constraint = eq(fresh_symbolic_subset, symbolicized_concrete_solution)
        model, _ = getModel(constraints + [scs_constraint] + [freshSubset_eq_left_constraint])

        if model is not None:
          concretized_symbolic_solution_alt = fresh_symbolic_subset.to_NaiveSubset(model)
          assert eq(concretized_symbolic_solution_alt, left), f"{left} vs. {concretized_symbolic_solution_alt}"  # lots of things have gone wrong if this assertion ever fails
          return True
        else:
          raise Exception(f"Solver produced unexpected alternative and does not agree with concrete implementation.\nExpected: '{left}'\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{left}\n{right}\n{subsets}\n{constraints}")
    else:
      raise Exception(f"Unexpected lack of solution from solver.\nExpected: '{left}'\nbut got: nothing\nfrom:\n{f}\n{left}\n{right}\n{subsets}\n{constraints}")
  else:
    symbolic_left, left_constraint = SymbolicVectorSubset.mk_from_NaiveSubset(f"concrete_left", u, left)

    symbolic_constraint: Constraint = f( symbolic_left  # type: ignore
                                       , right_symbolic
                                       , set(subsets_symbolic)
                                       )

    constraints = [symbolic_constraint] + [right_constraint] + subsets_constraints + [left_constraint]
    model, _    = getModel(constraints)

    if model is not None:
      concretized_symbolic_solution = symbolic_left.to_NaiveSubset(model)
      assert eq(concretized_symbolic_solution, left), f"{left} vs. {concretized_symbolic_solution}"  # lots of things have gone wrong if this assertion ever fails
      raise Exception(f"Symbolic implementation thinks `left` is a solution where concrete implementation does NOT.\nExpected: no solution\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{left}\n{right}\n{subsets}\n{constraints}")
    else:
      return True

def check_consistency_oneOneOne( f: Callable[[Subset, Subset, Subset], Bool]
                                , subset: NaiveSubset[A]
                                , left: NaiveSubset[A]
                                , right: NaiveSubset[A]
                                , subset_is_unique_solution: bool = True
                                , addFinalNullPSArg: bool = False
                                ):
  if addFinalNullPSArg:
    g = lambda subset, left, right: f(subset, left, right, None)  # type: ignore
  else:
    g = f

  concrete_result = g( subset
                     , left
                     , right
                     )

  u = tuple(sorted(left.universe))  # type: ignore
  left_symbolic, left_constraint   = SymbolicVectorSubset.mk_from_NaiveSubset( f"concrete_left"
                                                                             , u
                                                                             , left
                                                                             )
  right_symbolic, right_constraint = SymbolicVectorSubset.mk_from_NaiveSubset( f"concrete_right"
                                                                             , u
                                                                             , right
                                                                             )

  if concrete_result:

    fresh_symbolic_subset = SymbolicVectorSubset.mk("fresh", u)
    symbolic_constraint: Constraint = g( fresh_symbolic_subset
                                       , left_symbolic
                                       , right_symbolic
                                       )

    constraints = [symbolic_constraint] + [right_constraint] + [left_constraint]
    model, _    = getModel(constraints)

    if model is not None:
      concretized_symbolic_solution = fresh_symbolic_subset.to_NaiveSubset(model)

      if eq(subset, concretized_symbolic_solution):
        return True
      elif subset_is_unique_solution:
        raise Exception(f"Solver produced unexpected alternative.\nExpected: '{subset}'\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{subset}\n{left}\n{right}\n{constraints}")
      else:
        symbolicized_concrete_solution, scs_constraint = SymbolicVectorSubset.mk_from_NaiveSubset("concrete_subset", u, subset)
        freshSubset_eq_left_constraint: Constraint = eq(fresh_symbolic_subset, symbolicized_concrete_solution)
        model, _ = getModel(constraints + [scs_constraint] + [freshSubset_eq_left_constraint])

        if model is not None:
          concretized_symbolic_solution_alt = fresh_symbolic_subset.to_NaiveSubset(model)
          assert eq(concretized_symbolic_solution_alt, subset), f"{subset} vs. {concretized_symbolic_solution_alt}"  # lots of things have gone wrong if this assertion ever fails
          return True
        else:
          raise Exception(f"Solver produced unexpected alternative and does not agree with concrete implementation.\nExpected: '{subset}'\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{subset}\n{left}\n{right}\n{constraints}")
    else:
      raise Exception(f"Unexpected lack of solution from solver.\nExpected: '{subset}'\nbut got: nothing\nfrom:\n{f}\n{subset}\n{left}\n{right}\n{constraints}")
  else:
    symbolic_subset, subset_constraint = SymbolicVectorSubset.mk_from_NaiveSubset(f"concrete_subset", u, subset)

    symbolic_constraint: Constraint = g( symbolic_subset  # type: ignore
                                       , left_symbolic
                                       , right_symbolic
                                       )

    constraints = [symbolic_constraint] + [right_constraint] + [left_constraint] + [subset_constraint]
    model, _    = getModel(constraints)

    if model is not None:
      concretized_symbolic_solution = symbolic_subset.to_NaiveSubset(model)
      assert eq(concretized_symbolic_solution, subset), f"{subset} vs. {concretized_symbolic_solution}"  # lots of things have gone wrong if this assertion ever fails
      raise Exception(f"Symbolic implementation thinks `subset` is a solution where concrete implementation does NOT.\nExpected: no solution\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{subset}\n{left}\n{right}\n{constraints}")
    else:
      return True

def check_consistency_oneOneOneMany( f: Callable[[Subset, Subset, Subset, Set[Subset]], Bool]
                                   , subset: NaiveSubset[A]
                                   , left: NaiveSubset[A]
                                   , right: NaiveSubset[A]
                                   , subsets: Set[NaiveSubset[A]]
                                   , subset_is_unique_solution: bool = True
                                   , addFinalNullPSArg: bool = False
                                   ):
  if addFinalNullPSArg:
    g = lambda subset, left, right, subsets: f(subset, left, right, subsets, None)  # type: ignore
  else:
    g = f

  concrete_result = g( subset
                     , left
                     , right
                     , subsets
                     )

  u = tuple(sorted(left.universe))  # type: ignore
  left_symbolic, left_constraint   = SymbolicVectorSubset.mk_from_NaiveSubset( f"concrete_left"
                                                                             , u
                                                                             , left
                                                                             )
  right_symbolic, right_constraint = SymbolicVectorSubset.mk_from_NaiveSubset( f"concrete_right"
                                                                             , u
                                                                             , right
                                                                             )

  def _mk(identifier: str, ns: NaiveSubset[A]) -> Tuple[SymbolicVectorSubset[A], Constraint]:
    return SymbolicVectorSubset.mk_from_NaiveSubset(identifier, u, ns)
  subsets_plus_constraints = [ _mk(f"set_{i}", s)
                               for i,s in enumerate(subsets)
                             ]
  subsets_symbolic: List[SymbolicVectorSubset[A]] = lmap(fst, subsets_plus_constraints)
  subsets_constraints: List[Constraint]           = lmap(snd, subsets_plus_constraints)

  if concrete_result:

    fresh_symbolic_subset = SymbolicVectorSubset.mk("fresh", u)
    symbolic_constraint: Constraint = g( fresh_symbolic_subset
                                       , left_symbolic
                                       , right_symbolic
                                       , set(subsets_symbolic)
                                       )

    constraints = [symbolic_constraint] + [right_constraint] + [left_constraint] + subsets_constraints
    model, _    = getModel(constraints)

    if model is not None:
      concretized_symbolic_solution = fresh_symbolic_subset.to_NaiveSubset(model)

      if eq(subset, concretized_symbolic_solution):
        return True
      elif subset_is_unique_solution:
        raise Exception(f"Solver produced unexpected alternative.\nExpected: '{subset}'\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{subset}\n{left}\n{right}\n{subsets}\n{constraints}")
      else:
        symbolicized_concrete_solution, scs_constraint = SymbolicVectorSubset.mk_from_NaiveSubset("concrete_subset", u, subset)
        freshSubset_eq_left_constraint: Constraint = eq(fresh_symbolic_subset, symbolicized_concrete_solution)
        model, _ = getModel(constraints + [scs_constraint] + [freshSubset_eq_left_constraint])

        if model is not None:
          concretized_symbolic_solution_alt = fresh_symbolic_subset.to_NaiveSubset(model)
          assert eq(concretized_symbolic_solution_alt, subset), f"{subset} vs. {concretized_symbolic_solution_alt}"  # lots of things have gone wrong if this assertion ever fails
          return True
        else:
          raise Exception(f"Solver produced unexpected alternative and does not agree with concrete implementation.\nExpected: '{subset}'\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{subset}\n{left}\n{right}\n{subsets}\n{constraints}")
    else:
      raise Exception(f"Unexpected lack of solution from solver.\nExpected: '{subset}'\nbut got: nothing\nfrom:\n{f}\n{subset}\n{left}\n{right}\n{subsets}\n{constraints}")
  else:
    symbolic_subset, subset_constraint = SymbolicVectorSubset.mk_from_NaiveSubset(f"concrete_subset", u, subset)

    symbolic_constraint: Constraint = g( symbolic_subset  # type: ignore
                                       , left_symbolic
                                       , right_symbolic
                                       , set(subsets_symbolic)
                                       )

    constraints = [symbolic_constraint] + [right_constraint] + [left_constraint] + subsets_constraints + [subset_constraint]
    model, _    = getModel(constraints)

    if model is not None:
      concretized_symbolic_solution = symbolic_subset.to_NaiveSubset(model)
      assert eq(concretized_symbolic_solution, subset), f"{subset} vs. {concretized_symbolic_solution}"  # lots of things have gone wrong if this assertion ever fails
      raise Exception(f"Symbolic implementation thinks `subset` is a solution where concrete implementation does NOT.\nExpected: no solution\nbut got: '{concretized_symbolic_solution}'\nfrom:\n{f}\n{subset}\n{left}\n{right}\n{subsets}\n{constraints}")
    else:
      return True


# TODO - add `SymbolicArraySubset` tests

# Round-trip conversion

@given(_strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_conversion(value: NaiveSubset[int]):
  assert check_SymbolicVectorSubset_conversion(value)

# Eq

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_eq(left: NaiveSubset[int], right: NaiveSubset[int]):
  assert check_consistency_oneOne( eq, left, right, left_is_unique_solution=False)

# should also cover similar testing for `distinct`
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_neq(left: NaiveSubset[int], right: NaiveSubset[int]):
  assert check_consistency_oneOne( neq, left, right, left_is_unique_solution=False)

# TODO waiting for `check_consistency_many` implementation - `eq1`
# @given(_strategy_NaiveSubset_Set_int())
# def test_SymbolicVectorSubset_eq1(subsets: Set[NaiveSubset[int]]):
#   assert check_consistency_many( eq1, subsets, subsets_are_unique_solution=True )

# TODO waiting for `check_consistency_many` implementation - `neq1`
# @given(_strategy_NaiveSubset_Set_int())
# def test_SymbolicVectorSubset_neq1(subsets: Set[NaiveSubset[int]]):
#   assert check_consistency_many( neq1, subsets, subsets_are_unique_solution=True )

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_Set_int())
def test_SymbolicVectorSubset_eq2(subset: NaiveSubset[int], subsets: Set[NaiveSubset[int]]):
  assert check_consistency_oneMany( eq2, subset, subsets, subset_is_unique_solution=False, addFinalNullPSArg=False )

# should also cover similar testing for `elementOf`
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_Set_int())
def test_SymbolicVectorSubset_eq3(subset: NaiveSubset[int], subsets: Set[NaiveSubset[int]]):
  assert check_consistency_oneMany( eq3, subset, subsets, subset_is_unique_solution=False, addFinalNullPSArg=False )

# TODO waiting for `check_consistency_manyMany` implementation - `eq4`
# @given(_strategy_NaiveSubset_Set_int(), _strategy_NaiveSubset_Set_int())
# def test_SymbolicVectorSubset_eq4(lefts: Set[NaiveSubset[int]], rights: Set[NaiveSubset[int]]):
#   assert check_consistency_manyMany( eq4, lefts, rights, lefts_are_unique_solution=True )

# TODO waiting for `check_consistency_manyMany` implementation - `eq5`
# @given(_strategy_NaiveSubset_Set_int(), _strategy_NaiveSubset_Set_int())
# def test_SymbolicVectorSubset_eq5(lefts: Set[NaiveSubset[int]], rights: Set[NaiveSubset[int]]):
#   assert check_consistency_manyMany( eq5, lefts, rights, lefts_are_unique_solution=True )

@given(_strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_Eq_law_reflexivity_forAll(subset: NaiveSubset[int]):
  assert check_consistency_one( SE.law_reflexivity_forAll, subset, subset_is_unique_solution=False, addFinalNullPSArg=False )

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_Eq_law_transitivity_forAll(subset: NaiveSubset[int], left: NaiveSubset[int], right: NaiveSubset[int]):
  assert check_consistency_oneOneOne( SE.law_transitivity_forAll, subset, left, right, subset_is_unique_solution=False, addFinalNullPSArg=False)

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_Eq_law_symmetry_forAll(left: NaiveSubset[int], right: NaiveSubset[int]):
  assert check_consistency_oneOne( SE.law_symmetry_forAll, left, right, left_is_unique_solution=False)

# Preorder

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_le(left: NaiveSubset[int], right: NaiveSubset[int]):
  assert check_consistency_oneOne( le, left, right, left_is_unique_solution=False)

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_ge(left: NaiveSubset[int], right: NaiveSubset[int]):
  assert check_consistency_oneOne( ge, left, right, left_is_unique_solution=False)

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_comparable(left: NaiveSubset[int], right: NaiveSubset[int]):
  assert check_consistency_oneOne( comparable, left, right, left_is_unique_solution=False)

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_lt(left: NaiveSubset[int], right: NaiveSubset[int]):
  assert check_consistency_oneOne( lt, left, right, left_is_unique_solution=False)

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_gt(left: NaiveSubset[int], right: NaiveSubset[int]):
  assert check_consistency_oneOne( gt, left, right, left_is_unique_solution=False)

# should also cover similar testing for `is_between`
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_is_in_interval(subset: NaiveSubset[int], left: NaiveSubset[int], right: NaiveSubset[int]):
  assert check_consistency_oneOneOne( is_in_interval, subset, left, right, subset_is_unique_solution=False, addFinalNullPSArg=False )

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_Set_int())
def test_SymbolicVectorSubset_is_maximal(subset: NaiveSubset[int], subsets: Set[NaiveSubset[int]]):
  assert check_consistency_oneMany( is_maximal, subset, subsets, subset_is_unique_solution=False, addFinalNullPSArg=False )

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_Set_int())
def test_SymbolicVectorSubset_is_minimal(subset: NaiveSubset[int], subsets: Set[NaiveSubset[int]]):
  assert check_consistency_oneMany( is_minimal, subset, subsets, subset_is_unique_solution=False, addFinalNullPSArg=False )

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_Set_int())
def test_SymbolicVectorSubset_is_least(subset: NaiveSubset[int], subsets: Set[NaiveSubset[int]]):
  assert check_consistency_oneMany( is_least, subset, subsets, subset_is_unique_solution=False, addFinalNullPSArg=False )

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_Set_int())
def test_SymbolicVectorSubset_is_greatest(subset: NaiveSubset[int], subsets: Set[NaiveSubset[int]]):
  assert check_consistency_oneMany( is_greatest, subset, subsets, subset_is_unique_solution=False, addFinalNullPSArg=False )

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_Set_int())
def test_SymbolicVectorSubset_is_lower_bound(subset: NaiveSubset[int], subsets: Set[NaiveSubset[int]]):
  assert check_consistency_oneMany( is_lower_bound, subset, subsets, subset_is_unique_solution=False, addFinalNullPSArg=False )

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_Set_int())
def test_SymbolicVectorSubset_is_upper_bound(subset: NaiveSubset[int], subsets: Set[NaiveSubset[int]]):
  assert check_consistency_oneMany( is_upper_bound, subset, subsets, subset_is_unique_solution=False, addFinalNullPSArg=False )

# should also cover similar testing for `is_meet`
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_is_least_upper_bound(subset: NaiveSubset[int], left: NaiveSubset[int], right: NaiveSubset[int]):
  assert check_consistency_oneOneOne( is_least_upper_bound, subset, left, right, subset_is_unique_solution=True, addFinalNullPSArg=True )

# should also cover similar testing for `is_join`
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_is_greatest_lower_bound(subset: NaiveSubset[int], left: NaiveSubset[int], right: NaiveSubset[int]):
  assert check_consistency_oneOneOne( is_greatest_lower_bound, subset, left, right, subset_is_unique_solution=True, addFinalNullPSArg=True )

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_PS_int())
def test_SymbolicVectorSubset_is_least_upper_bound_ps(subset: NaiveSubset[int], left: NaiveSubset[int], right: NaiveSubset[int], ps: Set[NaiveSubset[int]]):
  assert check_consistency_oneOneOneMany( is_least_upper_bound, subset, left, right, ps, subset_is_unique_solution=True)

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_PS_int())
def test_SymbolicVectorSubset_is_greatest_lower_bound_ps(subset: NaiveSubset[int], left: NaiveSubset[int], right: NaiveSubset[int], ps: Set[NaiveSubset[int]]):
  assert check_consistency_oneOneOneMany( is_greatest_lower_bound, subset, left, right, ps, subset_is_unique_solution=True)

# should also cover similar testing for `is_meet1`
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_Set_int())
def test_SymbolicVectorSubset_is_greatest_lower_bound1(subset: NaiveSubset[int], subsets: Set[NaiveSubset[int]]):
  assert check_consistency_oneMany( is_greatest_lower_bound1, subset, subsets, subset_is_unique_solution=True, addFinalNullPSArg=True )

# should also cover similar testing for `is_join1`
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_Set_int())
def test_SymbolicVectorSubset_is_least_upper_bound1(subset: NaiveSubset[int], subsets: Set[NaiveSubset[int]]):
  assert check_consistency_oneMany( is_least_upper_bound1, subset, subsets, subset_is_unique_solution=True, addFinalNullPSArg=True )

# should also cover similar testing for `has_join`
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_PS_int())
def test_SymbolicVectorSubset_has_least_upper_bound(left: NaiveSubset[int], right: NaiveSubset[int], ps: Set[NaiveSubset[int]]):
  assert check_consistency_oneOneMany( has_least_upper_bound, left, right, ps, left_is_unique_solution=False )

# should also cover similar testing for `has_meet`
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_PS_int())
def test_SymbolicVectorSubset_has_greatest_lower_bound(left: NaiveSubset[int], right: NaiveSubset[int], ps: Set[NaiveSubset[int]]):
  assert check_consistency_oneOneMany( has_greatest_lower_bound, left, right, ps, left_is_unique_solution=False )

# TODO waiting for `check_consistency_many` implementation - `has_greatest_lower_bound1` - `has_meet1`
# # should also cover similar testing for `has_meet1`
# @given(_strategy_NaiveSubset_Set_int())
# def test_SymbolicVectorSubset_has_greatest_lower_bound1(subsets: Set[NaiveSubset[int]]):
#   assert check_consistency_many( has_greatest_lower_bound1, subsets, subsets_are_unique_solution=True )

# TODO waiting for `check_consistency_many` implementation - `has_least_upper_bound1` - `has_join1`
# # should also cover similar testing for `has_join1`
# @given(_strategy_NaiveSubset_Set_int())
# def test_SymbolicVectorSubset_has_least_upper_bound1(subsets: Set[NaiveSubset[int]]):
#   assert check_consistency_many( has_least_upper_bound1, subsets, subsets_are_unique_solution=True )

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_PS_int())
def test_SymbolicVectorSubset_covers(left: NaiveSubset[int], right: NaiveSubset[int], ps: Set[NaiveSubset[int]]):
  assert check_consistency_oneOneMany( covers, left, right, ps, left_is_unique_solution=False )

# TODO waiting for `check_consistency_many` implementation - `is_chain`
# @given(_strategy_NaiveSubset_Set_int())
# def test_SymbolicVectorSubset_is_chain(subsets: Set[NaiveSubset[int]]):
#   assert check_consistency_many( is_chain, subsets, subsets_are_unique_solution=True )

@given(_strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_Preorder_law_reflexivity_forAll(subset: NaiveSubset[int]):
  assert check_consistency_one( SO.law_reflexivity_forAll, subset, subset_is_unique_solution=False, addFinalNullPSArg=False )

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_Preorder_law_transitivity_forAll(subset: NaiveSubset[int], left: NaiveSubset[int], right: NaiveSubset[int]):
  assert check_consistency_oneOneOne( SO.law_transitivity_forAll, subset, left, right, subset_is_unique_solution=False, addFinalNullPSArg=False )

# LowerBounded

@given(_strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_is_global_lower_bound(subset: NaiveSubset[int]):
  assert check_consistency_one( is_global_lower_bound, subset, subset_is_unique_solution=True, addFinalNullPSArg=True )

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_PS_int())
def test_SymbolicVectorSubset_is_global_lower_bound_ps(subset: NaiveSubset[int], ps: Set[NaiveSubset[int]]):
  assert check_consistency_oneMany( is_global_lower_bound, subset, ps, subset_is_unique_solution=True, addFinalNullPSArg=False )

@given(_strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_is_atom(subset: NaiveSubset[int]):
  assert check_consistency_one( is_atom, subset, subset_is_unique_solution=False, addFinalNullPSArg=True )

@settings(deadline=40000)
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_PS_int())
def test_SymbolicVectorSubset_is_atom_ps(subset: NaiveSubset[int], ps: Set[NaiveSubset[int]]):
  assert check_consistency_oneMany( is_atom, subset, ps, subset_is_unique_solution=False, addFinalNullPSArg=False )

# TODO waiting for `check_consistency_many` implementation - `is_atom1`
# @given(_strategy_NaiveSubset_Set_int())
# def test_SymbolicVectorSubset_is_atom1(subsets: Set[NaiveSubset[int]]):
#   assert check_consistency_many( is_atom1, subsets, subsets_are_unique_solution=True )

# TODO waiting for `check_consistency_many` implementation - `law_lowerBounded`
# @given(_strategy_NaiveSubset_Set_int())
# def test_SymbolicVectorSubset_law_lowerBounded(subsets: Set[NaiveSubset[int]]):
#   assert check_consistency_many( law_lowerBounded, subsets, subsets_are_unique_solution=True )

# UpperBounded

@given(_strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_is_global_upper_bound(subset: NaiveSubset[int]):
  assert check_consistency_one( is_global_upper_bound, subset, subset_is_unique_solution=True, addFinalNullPSArg=True )


@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_PS_int())
def test_SymbolicVectorSubset_is_global_upper_bound_ps(subset: NaiveSubset[int], ps: Set[NaiveSubset[int]]):
  assert check_consistency_oneMany( is_global_upper_bound, subset, ps, subset_is_unique_solution=True, addFinalNullPSArg=False )

# TODO waiting for `check_consistency_many` implementation - `law_UpperBounded`
# @given(_strategy_NaiveSubset_Set_int())
# def test_SymbolicVectorSubset_law_upperBounded(subsets: Set[NaiveSubset[int]]):
#   assert check_consistency_many( law_upperBounded, subsets, subsets_are_unique_solution=True )

# PartialOrder

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int())
def test_SymbolicVectorSubset_Preorder_law_antisymmetric_forAll(left: NaiveSubset[int], right: NaiveSubset[int]):
  assert check_consistency_oneOne( law_antisymmetric_forAll, left, right, left_is_unique_solution=False)

# MeetSemilattice

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_PS_int())
def test_SymbolicVectorSubset_law_meetExists_forAll(left: NaiveSubset[int], right: NaiveSubset[int], ps: Set[NaiveSubset[int]]):
  assert check_consistency_oneOneMany( law_meetExists_forAll, left, right, ps, left_is_unique_solution=False )

# JoinSemilattice

@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_PS_int())
def test_SymbolicVectorSubset_law_joinExists_forAll(left: NaiveSubset[int], right: NaiveSubset[int], ps: Set[NaiveSubset[int]]):
  assert check_consistency_oneOneMany( law_joinExists_forAll, left, right, ps, left_is_unique_solution=False )

# BoundedLattice

@settings(deadline=40000)
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_int(), _strategy_NaiveSubset_PS_int())
def test_SymbolicVectorSubset_complementary(left: NaiveSubset[int], right: NaiveSubset[int], ps: Set[NaiveSubset[int]]):
  assert check_consistency_oneOneMany( complementary, left, right, ps, left_is_unique_solution=True )

# ComplementedLattice

@settings(deadline=60000)
@given(_strategy_NaiveSubset_int(), _strategy_NaiveSubset_PS_int())
def test_SymbolicVectorSubset_law_complementExists_forAll(subset: NaiveSubset[int], subsets: Set[NaiveSubset[int]]):
  assert check_consistency_oneMany( law_complementExists_forAll, subset, subsets, subset_is_unique_solution=False, addFinalNullPSArg=False )
