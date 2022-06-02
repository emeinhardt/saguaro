# from collections.abc import Collection, Mapping, Sequence
# import collections.abc as cabc
import typing
# from collections.abc import Collection, Sequence#, Mapping
from typing import get_args#, overload, TypeVar
from typing import Union#,Optional, Collection, Sequence
from typing import Collection, Sequence, Tuple, List, Set, FrozenSet
from classes import AssociatedType, Supports, typeclass

# from funcy import lmap
# from functools import reduce

# import hypothesis
# from hypothesis import given, strategies as st
import pytest

import z3

import saguaro.utilities as SU
from saguaro.utilities import foldl, A


# BASIC TESTS

# def test_should_fail():
#   assert False == True

def test_should_pass():
  assert False == False

# See https://classes.readthedocs.io/en/latest/pages/generics.html#complex-concrete-generics
class UserTupleMeta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return (
            isinstance(arg, tuple) and
            isinstance(arg[0], str) and
            isinstance(arg[1], bool)
            )
    except IndexError:
      return False

class UserTuple(Tuple[str, bool], metaclass=UserTupleMeta): ...

@typeclass
def get_name(instance) -> str: ...

@get_name.instance(delegate=UserTuple)
def _get_name_user_dict(instance: Tuple[str, bool]) -> str:
  return instance[0]

# Make the simplest thing that almost looks like what we have...
class boolListMeta(type):
   def __instancecheck__(cls, arg: object) -> bool:
    try:
      return (
               isinstance(arg, list) and
               (
                 isinstance(arg[0], bool) or
                 len(arg) == 0
               )
             )
    except IndexError:
      return False

class BoolList(List[bool], metaclass=boolListMeta): ...

@typeclass
def get_and(instance) -> bool: ...

@get_and.instance(delegate=BoolList)
def _get_and_BoolList(instance: List[bool]) -> str:
  return foldl(lambda p,q: p and q, [True])(instance)


# Take it another step - introduce union types
# from saguaro._Boolean import Bool
Bool = Union[bool, z3.BoolRef]

class UnionListMeta(type):
   def __instancecheck__(cls, arg: object) -> bool:
    try:
      return (
               isinstance(arg, list) and
               (
                  len(arg) == 0 or
                  (
                    type(arg[0]) in get_args(Bool)
                    # isinstance(arg[0], bool) or
                    # isinstance(arg[0], z3.BoolRef)
                  )
               )
             )
    except e:
      return False

class UnionList(List[Bool], metaclass=UnionListMeta): ...

@typeclass
def get_And(instance) -> bool: ...

@get_And.instance(delegate=UnionList)
def _get_And_UnionList(instance: List[Bool]) -> str:
  return foldl(lambda p,q: p and q, [True])(instance)


# Next step: can you check for sequences inside of the metaclass instancecheck?
class UnionSequenceMeta(type):
   def __instancecheck__(cls, arg: object) -> bool:
    try:
      return (
               isinstance(arg, Sequence) and
               (
                  len(arg) == 0 or
                  (
                    type(arg[0]) in get_args(Bool)
                    # isinstance(arg[0], bool) or
                    # isinstance(arg[0], z3.BoolRef)
                  )
               )
             )
    except e:
      return False

# This is how to actually define instances for non-concrete built-in container generics
class UnionSeq(metaclass=UnionSequenceMeta): ...
class UnionSeq_tuple(tuple[Bool], UnionSeq): ...
class UnionSeq_list(list[Bool], UnionSeq): ...

# class UnionSeq_tuple(tuple[Bool], metaclass=UnionSequenceMeta): ...
# class UnionSeq_list(list[Bool], metaclass=UnionSequenceMeta): ...
# class UnionSeq(list[Bool], metaclass=UnionSequenceMeta): ... # works, but won't actually work with any Sequence other than List
# class UnionSeq(cabc.Sequence, metaclass=UnionSequenceMeta): ...
# class UnionSeq(cabc.Sequence[Bool], metaclass=UnionSequenceMeta): ...
# class UnionSeq(Sequence, metaclass=UnionSequenceMeta): ...
# class UnionSeq(Sequence[Bool], metaclass=UnionSequenceMeta): ...

@typeclass
def get_Ands(instance) -> Bool: ...

@get_Ands.instance(delegate=UnionSeq)
def _get_Ands_UnionSeq(instance: Sequence[Bool]) -> str:
# def _get_Ands_UnionSeq(instance: List[Bool]) -> str:
  return foldl(lambda p,q: p and q, [True])(instance)


# class Andables(AssociatedType[A]): ...
class Andables(AssociatedType): ...

@typeclass(Andables)
# def get_Andz(instance: Union[Supports[Andables[A]], Sequence[Supports[Andables[A]]]]) -> Bool: ...
def get_Andz(instance: Union[Supports[Andables], Sequence[Supports[Andables]]]) -> Bool: ...
# def get_Andz(instance: Supports[Andables]) -> Bool: ...
# def get_Andz(instance) -> Bool: ...

@get_Andz.instance(delegate=UnionSeq)
def _get_Andz_UnionSeq(instance: Sequence[Bool]) -> str:
# def _get_Andz_UnionSeq(instance: List[Bool]) -> str:
  return foldl(lambda p,q: p and q, [True])(instance)

# @get_Andz.instance(Bool)
# def _get_Andz_Bool(instance: Bool) -> str:
#   return False and instance

@get_Andz.instance(bool)
def _get_Andz_Bool(instance: bool) -> str:
  return True and instance

@get_Andz.instance(z3.BoolRef)
def _get_Andz_Bool(instance: z3.BoolRef) -> str:
  return True and instance


def test_typeclass():
  assert     get_name(('sobolevn', True)) == 'sobolevn'

  assert _get_Andz_Bool(True)
  assert _get_Andz_Bool([True])
  _ = _get_Andz_Bool(z3.Not(False))
  _ = _get_Andz_Bool([z3.Not(False), True])
  _ = _get_Andz_Bool([True, z3.Not(False)])

  assert     get_and([True, True])
  assert not get_and([True, False])
  assert not get_and([False])
  assert     get_And([True, True])
  assert not get_And([True, False])
  assert not get_And([False])
  assert     get_Ands([True, True])
  assert not get_Ands([True, False])
  assert not get_Ands([False])
  assert     get_Andz([True, True])
  assert not get_Andz([True, False])
  assert not get_Andz([False])

  assert     get_Ands(tuple([True, True]))
  assert not get_Ands(tuple([True, False]))
  assert not get_Ands(tuple([False]))
  assert     get_Andz(tuple([True, True]))
  assert not get_Andz(tuple([True, False]))
  assert not get_Andz(tuple([False]))
