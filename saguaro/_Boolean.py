'''
Contains type- and testing-related code for dealing with one/both of
 - concrete Python boolean values (`bool`)
 - symbolic z3 boolean values (`z3.BoolRef`)
including
 - a union type `Bool`.
 - some types (prefixed with _) that are there to aid type inference.
 - some functions for generating values for testing ("search
   strategies" for `hypothesis`).

The `Boolean` typeclass is purely used to abstract over bool vs. z3.BoolRef in
Subset.py. See the docstring for the `Boolean` typeclass in this module for
more context.


It is a mundane example of a typeclass being used straightforwardly as a common
interface for distinct implementations, with implementations indexed by type -
in this case, `bool` or `z3.BoolRef`. (It also has examples of default
implementations and `mypy`'s @overload annotation.)

As the module's leading underscore should suggest and as the `Boolean` docstring
elaborates, this module is an implementation detail of other modules - it's not
intended to be a model of a mathematical structure (+ instances) intended for
investigation in the context of an SMT solver, it is an auxiliary detail FOR
such investigations.
'''

import typing
from typing import get_args, overload, TypeVar
from typing import Optional, Union
from typing import Collection, Sequence, Tuple, List, Set, FrozenSet

from classes import AssociatedType, Supports, typeclass

from hypothesis import strategies as st
from hypothesis.strategies import SearchStrategy, sampled_from

from funcy import lmap

import z3

from saguaro.utilities import identity, peek, foldl
from saguaro.utilities import mk_UnknownTypeError, mk_Boolean_OverloadingError \
                            , mk_Boolean_TypeParameterError, mk_Boolean_OverloadingError1 \


#####################################################################################
# `bool` / `z3.BoolRef` union type + typecasting + special types for type inference #
#####################################################################################

# NB
#  - `bool` and `z3.BoolRef` are not equal types
#  - Neither is an instance of the other

Bool = Union[bool, z3.BoolRef]
# SymBool     = z3.BoolRef # synonym intended for variable declarations
Constraint  = z3.BoolRef # synonym intended for pretty much every other kind of z3 expression
Constraints = Collection[z3.BoolRef]

def id_Bool(b: Bool) -> Bool:
  return identity(b)

def all_Bool(bs: Collection[Bool]) -> Bool:
  def and_op(p: Bool, q: Bool) -> Bool:
    return p and q
  return foldl(and_op, True)(bs)

def any_Bool(bs: Collection[Bool]) -> Bool:
  def or_op(p: Bool, q: Bool) -> Bool:
    return p or q
  return foldl(or_op, False)(bs)

# Typecasting between `bool` and `z3.BoolRef`

def bool_to_BoolRef(b: bool, identifier: str) -> Tuple[z3.BoolRef, z3.BoolRef]:
  b_symbolic = z3.Bool(identifier)
  return (b_symbolic, b_symbolic == b)

def bool_to_BoolRef1(b: bool) -> z3.BoolRef:
  return z3.BoolVal(b)

def boolPair_to_BoolRef(left: bool, right: bool, identifier: str) -> Tuple[Tuple[z3.BoolRef, z3.BoolRef], Tuple[z3.BoolRef, z3.BoolRef]]:
  left_symbolic, right_symbolic = z3.Bool(f"{identifier}_left"), z3.Bool(f"{identifier}_right")
  return ((left_symbolic, left_symbolic == left), (right_symbolic, right_symbolic == right))

def boolPair_to_BoolRef1(left: bool, right: bool) -> Tuple[z3.BoolRef, z3.BoolRef]:
  return z3.BoolVal(left), z3.BoolVal(right)

def bools_to_BoolRef(bs: Collection[bool], identifier: str) -> Tuple[Collection[z3.BoolRef], Collection[z3.BoolRef]]:
  if type(bs) in (list, tuple, set, frozenset):
    outtype = type(bs)
  else:
    raise mk_UnknownTypeError(bs, [list, tuple, set, frozenset])
  bs_symbolic    = outtype(z3.Bool(f"{identifier}_{i}") for i in range(len(bs)))  # type: ignore
  bs_constraints = outtype(b_symbolic == b for b_symbolic, b in zip(bs_symbolic, bs))  # type: ignore
  return (bs_symbolic, bs_constraints)

def bools_to_BoolRef1(bs: Collection[bool]) -> Collection[z3.BoolRef]:
  if type(bs) in (list, tuple, set, frozenset):
    outtype = type(bs)
  else:
    raise mk_UnknownTypeError(bs, [list, tuple, set, frozenset])
  return outtype(z3.BoolVal(b) for b in bs)  # type: ignore


# Classes that only exist to aid typechecking

###
# Per
#   https://classes.readthedocs.io/en/latest/pages/generics.html
# no variant of either of the "__instancecheck__" metaclasses and classes below
# will work right now because
#  (1) both of the metaclasses below need to be subtypes of the metaclasses of
#      all their bases to be used as the meta-class for
#        _Collection_Bool # base is one of `abc.`
#        _Sequence_Bool

# class _Collection_Object_Meta(type):
#   def __instancecheck__(cls, arg: object) -> bool:
#     try:
#       return isinstance(arg, Collection)
#     except Exception:
#       return False

# class _Collection_Object(metaclass=_Collection_Object_Meta): ...
# class _Collection_Object_FrozenSet(FrozenSet, _Collection_Object): ...
# class _Collection_Object_Set(Set, _Collection_Object): ...
# class _Collection_Object_Tuple(Tuple, _Collection_Object): ...
# class _Collection_Object_List(List, _Collection_Object): ...

# class _Collection_Bool_Meta(typing._GenericAlias):
# # class _Collection_Bool_Meta(typing._SpecialGenericAlias):
# # class _Collection_Bool_Meta(type(Collection[Bool])):
# class _Collection_Bool_Meta(type(Collection)):
class _Collection_Bool_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, Collection) \
             and (   len(arg) == 0 \
               or type(peek( arg )) in get_args(Bool) #TODO explain the relevance of get_args to typeclasses somewhere; link to https://stackoverflow.com/questions/48572831/how-to-access-the-type-arguments-of-typing-generic
               )
    except Exception:
      return False

class Collection_Bool(metaclass=_Collection_Bool_Meta): ...
class FrozenSet_Bool(FrozenSet[Bool], Collection_Bool): ...
class Set_Bool(Set[Bool], Collection_Bool): ...
# class Tuple_Bool(Tuple[Bool], Collection_Bool): ...
# class List_Bool(List[Bool], Collection_Bool): ...
# class _Collection_Bool(Collection, metaclass=_Collection_Bool_Meta): ...
# class _Collection_Bool(Collection[Bool], metaclass=_Collection_Bool_Meta): ...

# class _Sequence_Bool_Meta(typing._GenericAlias):
# class _Sequence_Bool_Meta(typing._SpecialGenericAlias):
# class _Sequence_Bool_Meta(type(Sequence[Bool])):
# class _Sequence_Bool_Meta(type(Sequence)):
class _Sequence_Bool_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, Sequence) \
             and (   len(arg) == 0 \
               or type(peek( arg )) in get_args(Bool) #TODO explain the relevance of get_args to typeclasses somewhere; link to https://stackoverflow.com/questions/48572831/how-to-access-the-type-arguments-of-typing-generic
               )
    except Exception:
      return False

class Sequence_Bool(metaclass=_Sequence_Bool_Meta): ...
class Tuple_Bool(Tuple[Bool], Sequence_Bool): ...
class List_Bool(List[Bool], Sequence_Bool): ...
# class _Sequence_Bool(Sequence, metaclass=_Sequence_Bool_Meta): ...
# class _Sequence_Bool(Sequence[Bool], metaclass=_Sequence_Bool_Meta): ...


class _Collection_bool_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, Collection) \
             and (   len(arg) == 0 \
               or all([ isinstance(b, bool)
                       for b in arg
                     ])
               # or isinstance(peek(arg), bool)
               )
    except Exception:
      return False

class Collection_bool(metaclass=_Collection_bool_Meta): ...
class FrozenSet_bool(FrozenSet[bool], Collection_bool): ...
class Set_bool(Set[bool], Collection_bool): ...
# class Tuple_bool(Tuple[bool], Collection_bool): ...
# class List_bool(List[bool], Collection_bool): ...

class _Sequence_bool_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, Sequence) \
             and (   len(arg) == 0 \
               or all([ isinstance(b, bool)
                       for b in arg
                     ])
               # or isinstance(peek(arg), bool)
               )
    except Exception:
      return False

class Sequence_bool(metaclass=_Sequence_bool_Meta): ...
class Tuple_bool(Tuple[bool], Sequence_bool): ...
class List_bool(List[bool], Sequence_bool): ...

class _Collection_BoolRef_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, Collection) \
             and (   len(arg) == 0 \
               or any([ isinstance(b, z3.BoolRef)
                       for b in arg
                     ])
               # or isinstance(peek(arg), z3.BoolRef)
               )
    except Exception:
      return False

class Collection_BoolRef(metaclass=_Collection_BoolRef_Meta): ...
class FrozenSet_BoolRef(FrozenSet[z3.BoolRef], Collection_BoolRef): ...
class Set_BoolRef(Set[z3.BoolRef], Collection_BoolRef): ...
# class Tuple_BoolRef(Tuple[z3.BoolRef], Collection_BoolRef): ...
# class List_BoolRef(List[z3.BoolRef], Collection_BoolRef): ...

class _Sequence_BoolRef_Meta(type):
  def __instancecheck__(cls, arg: object) -> bool:
    try:
      return isinstance(arg, Sequence) \
             and (   len(arg) == 0 \
               or any([ isinstance(b, z3.BoolRef)
                       for b in arg
                     ])
               # or isinstance(peek(arg), z3.BoolRef)
               )
    except Exception:
      return False

class Sequence_BoolRef(metaclass=_Sequence_BoolRef_Meta): ...
class Tuple_BoolRef(Tuple[z3.BoolRef], Sequence_BoolRef): ...
class List_BoolRef(List[z3.BoolRef], Sequence_BoolRef): ...

# # class _Tuple_Bool_Meta(typing._GenericAlias):
# # class _Tuple_Bool_Meta(typing._SpecialGenericAlias):
# # class _Tuple_Bool_Meta(type(Tuple[Bool])):
# # class _Tuple_Bool_Meta(type(Tuple)):
# class _Tuple_Bool_Meta(type):
#   def __instancecheck__(cls, arg: object) -> bool:
#     try:
#       return isinstance(arg, tuple) \
#              and type(peek( arg )) in get_args(Bool) #TODO explain the relevance of get_args to typeclasses somewhere; link to https://stackoverflow.com/questions/48572831/how-to-access-the-type-arguments-of-typing-generic
#              # and isinstance(peek( arg ), Bool)
#     except IndexError:
#       return False

# # class _Tuple_Bool(Tuple, metaclass=_Tuple_Bool_Meta): ...
# class _Tuple_Bool(Tuple[Bool], metaclass=_Tuple_Bool_Meta): ...


# class _List_Bool_Meta(typing._GenericAlias):
# class _List_Bool_Meta(typing._SpecialGenericAlias):
# class _List_Bool_Meta(type(List[Bool])):
# class _List_Bool_Meta(type(List)):
# class _List_Bool_Meta(type):
#   def __instancecheck__(cls, arg: object) -> bool:
#     try:
#       print(f"isinstance(arg, list) = '{isinstance(arg, list)}'")
#       print(f"type(peek( arg )) = '{type(peek( arg ))}'")
#       print(f"get_args(Bool) = '{get_args(Bool)}'")
#       print(f"type(peek( arg )) in get_args(Bool) = '{type(peek( arg )) in get_args(Bool)}'")
#       return isinstance(arg, list) \
#              and type(peek( arg )) in get_args(Bool) #TODO explain the relevance of get_args to typeclasses somewhere; link to https://stackoverflow.com/questions/48572831/how-to-access-the-type-arguments-of-typing-generic
#              # and isinstance(peek( arg ), Bool)
#     except TypeError:
#       return False

# class _List_Bool(List, metaclass=_List_Bool_Meta): ...
# class _List_Bool(List[Bool], metaclass=_List_Bool_Meta): ...

# # class _FrozenSet_Bool_Meta(typing._GenericAlias):
# # class _FrozenSet_Bool_Meta(typing._SpecialGenericAlias):
# # class _FrozenSet_Bool_Meta(type(FrozenSet[Bool])):
# # class _FrozenSet_Bool_Meta(type(FrozenSet)):
# class _FrozenSet_Bool_Meta(type):
#   def __instancecheck__(cls, arg: object) -> bool:
#     try:
#       return isinstance(arg, frozenset) \
#              and type(peek( arg )) in get_args(Bool) #TODO explain the relevance of get_args to typeclasses somewhere; link to https://stackoverflow.com/questions/48572831/how-to-access-the-type-arguments-of-typing-generic
#              # and isinstance(peek( arg ), Bool)
#     except IndexError:
#       return False

# # class _FrozenSet_Bool(FrozenSet, metaclass=_FrozenSet_Bool_Meta): ...
# class _FrozenSet_Bool(FrozenSet[Bool], metaclass=_FrozenSet_Bool_Meta): ...


# # class _Set_Bool_Meta(typing._GenericAlias):
# # class _Set_Bool_Meta(typing._SpecialGenericAlias):
# # class _Set_Bool_Meta(type(Set[Bool])):
# # class _Set_Bool_Meta(type(Set)):
# class _Set_Bool_Meta(type):
#   def __instancecheck__(cls, arg: object) -> bool:
#     try:
#       return isinstance(arg, Set) \
#              and type(peek( arg )) in get_args(Bool) #TODO explain the relevance of get_args to typeclasses somewhere; link to https://stackoverflow.com/questions/48572831/how-to-access-the-type-arguments-of-typing-generic
#              # and isinstance(peek( arg ), Bool)
#     except IndexError:
#       return False

# # class _Set_Bool(Set, metaclass=_Set_Bool_Meta): ...
# class _Set_Bool(Set[Bool], metaclass=_Set_Bool_Meta): ...

##################################################
# Testing - 'search strategies' for `hypothesis` #
##################################################

def _strategy_bool() -> SearchStrategy[bool]:
  return st.booleans()

def _strategy_Collection_bool(max_size: int = 3) -> SearchStrategy[Collection[bool]]:
  return st.sets( elements = [True, False]
                , min_size = 0
                , max_size = max_size
                # , unique = True
                )

def _strategy_Set_bool(max_size: int = 3) -> SearchStrategy[Set[bool]]:
  return st.sets( elements = [True, False]
                , min_size = 0
                , max_size = max_size
                # , unique = True
                )

def _strategy_Sequence_bool(max_size: int = 3) -> SearchStrategy[Sequence[bool]]:
  return st.lists( elements = [True, False]
                 , min_size = 0
                 , max_size = max_size
                 , unique = True
                 )


def _strategy_List_bool(max_size: int = 3) -> SearchStrategy[List[bool]]:
  return st.lists( elements = [True, False]
                 , min_size = 0
                 , max_size = max_size
                 , unique = True
                 )

def _strategy_Tuple_bool(max_size: int = 3) -> SearchStrategy[Tuple[bool]]:
  return st.lists( elements = [True, False]
                 , min_size = 0
                 , max_size = max_size
                 , unique = True
                 )

def _strategy_BoolRef() -> SearchStrategy[z3.BoolRef]:
  return sampled_from( elements = lmap(z3.BoolVal, [True, False]) )

def _strategy_Collection_BoolRef() -> SearchStrategy[Collection[z3.BoolRef]]:
  return st.sets( elements = [z3.BoolVal(True), z3.BoolVal(False)]
                , min_size = 0
                , max_size = 5
                # , unique = True
                )

def _strategy_Sequence_BoolRef() -> SearchStrategy[Sequence[z3.BoolRef]]:
  return st.lists( elements = [z3.BoolVal(True), z3.BoolVal(False)]
                 , min_size = 0
                 , max_size = 5
                 , unique = True
                 )

def _strategy_Bool() -> SearchStrategy[Bool]:
  return z3.BoolVal(st.booleans())

def _strategy_Collection_Bool() -> SearchStrategy[Collection[Bool]]:
  return st.sets( elements = [z3.BoolVal(True), z3.BoolVal(False)]
                , min_size = 0
                , max_size = 5
                # , unique = True
                )

def _strategy_Sequence_Bool() -> SearchStrategy[Sequence[Bool]]:
  return st.lists( elements = [z3.BoolVal(True), z3.BoolVal(False)]
                 , min_size = 0
                 , max_size = 5
                 , unique = True
                 )



class Boolean(AssociatedType):
# class Boolean(AssociatedType[B]):
# class Boolean(AssociatedType[BB]): # this can't be right
#FIXME consider changing this to BB after
# class Boolean(AssociatedType[Bool]):
  """
  Because one big point of variation in this domain is that
   - concrete types have predicates and conditions expressed in terms of
     Python's native `bool` and boolean operations
   - symbolic types have predicates (constraints) and conditions expressed
     in terms of z3's z3.BoolRef and "boolean operations"/expression
     constructors
  (Note that every type is either concrete or symbolic, and hence type indexes
  which to expect.)

  This is, in fact, a concerete problem, because it prevents many default
  typeclass implementations from being written and forces them to be redudantly
  specified instead.

  As a solution, this typeclass abstracts over Python's bool vs. z3.BoolRef
  types and operators.

  NB
   - `bool` and `z3.BoolRef` are not equal types.
   - Neither is an instance of the other.
   - No mattter what you pass as an argument to a z3 term like
       `z3.Or(...)`    `z3.Not(...)`
     the term will be of type `z3.BoolRef`.
   - The type of other terms follows normal Python (and z3) evaluation rules and
     intuitions:
       - python boolean operators act like normal functions in that
            (1) if you "apply" e.g. `not` to a `bool` expression like `True`:
                   SB.Not(True)
                ==    not True
            then you can "evaluate" or "reduce" that expression to a new term:
                   SB.Not(True)
                ==    not True
                ==        False  # the result of evaluating the preceding term
            (2) They have "short-circut" evaluation behavior, as is common in
                comparable languages.
       - z3 boolean 'operators' *are not functions or operators* in the same
         sense python's are: *they do not evaluate to a Boolean*.
       - z3 boolean operators *build an expression* that is interpreted into
         e.g. a declaration or a constraint assertion.
  """

BB = TypeVar("BB", bound = Supports[Boolean])

@typeclass(Boolean)
def Not(b: BB) -> BB: ...
# def Not(b: Union[BB, Collection[BB]]) -> BB: ...
# def Not(b: Union[Bool, Collection[Bool]]) -> Bool: ...
@typeclass(Boolean) # Corresponds to "None", since And1 = "All" and Or1 = "Any"
def Not1(bs: Collection[BB]) -> BB: ...
# def Not1(bs: Collection[Bool]) -> Bool: ...
# def Not1(bs: List[Bool]) -> Bool: ...
# def Not1(bs: List) -> Bool: ...
# def Not1(bs: list) -> Bool: ...
# def Not1(bs) -> Bool: ...

# @Not1.instance(delegate = _Collection_Object_List)
# @Not1.instance(object)
# @Not1.instance(delegate = _Collection_Object)
@Not1.instance(delegate = Collection_Bool)
def _Not1_object(bs: Collection[BB]) -> BB:
# @Not1.instance(delegate = _List_Bool)
# def _not1_object(bs: List[BB]) -> BB:
# def _not1_object(bs: list) -> Bool:
# def _not1_object(bs: List) -> Bool:
# def _not1_object(bs: List[Bool]) -> Bool:
# def _not1_object(bs: _List_Bool) -> Bool:
# @Not1.instance(delegate = _Collection_Bool)
# def _not1_object(bs: _Collection_Bool) -> Bool:
# @Not1.instance(object)
# def _not1_object(bs):
# def _not1_object(bs: object) -> object:
# def _not1_object(bs: object) -> Bool:
# def _not1_object(bs: Collection) -> Bool:
# def _not1_object(bs: Collection[Bool]) -> Bool:
  return Not(Or1(bs))

# @overload
# def And(left: Collection[BB]) -> BB: ...
# @overload
# def And(left: BB, right: BB) -> BB: ...
@typeclass(Boolean)
def And(left: BB, right: BB) -> BB: ...
# def And(left: Union[BB, Collection[BB]], right: Optional[BB]) -> BB: ...
@typeclass(Boolean)
def And1(bs: Collection[BB]) -> BB: ...

# @overload
# def Or(left: BB, right: BB) -> BB: ...
# @overload
# def Or(left: Collection[BB]) -> BB: ...
@typeclass(Boolean)
def Or(left: BB, right: BB) -> BB: ...
# def Or(left: Union[BB, Collection[BB]], right: Optional[BB]) -> BB: ...
@typeclass(Boolean)
def Or1(bs: Collection[BB]) -> BB: ...

@typeclass(Boolean)
def Implies(left: BB, right: BB) -> BB: ...
# def Implies(left: Union[BB, Collection[BB]], right: BB) -> BB: ...
@typeclass(Boolean)
def Implies1(left: Collection[BB], right: BB) -> BB: ...

# @Implies.instance(object)
# @Implies.instance(delegate = _Collection_Bool)
@Implies.instance(object)
def _Implies_object(left: BB, right: BB) -> BB:
  if type(left) not in get_args(Bool):
    raise mk_UnknownTypeError(left, [Bool])
  elif type(right) not in get_args(Bool):
    raise mk_UnknownTypeError(right, [Bool])
  else:
    return Or(Not(left), right)
# def _Implies_object(left: Union[BB, Collection[BB]], right: BB) -> BB:
#   if type(left) in get_args(Bool):
#     return Or(Not(left), right)
#   elif isinstance(left, Collection):
#     if    ( len(get_args(left)) > 0 and Bool != get_args(left)[0] ) \
#        or ( len(         left)  > 0 and type(peek(left)) not in get_args(Bool) ):
#       raise mk_Boolean_TypeParameterError(left, Bool)
#       # raise Exception(f"left is a collection but not of Bool = `{Bool}`:\nleft = '{left}'")
#     return Implies1(left, right)
#   else:
#     raise mk_UnknownTypeError(left, [Union[Bool, Collection[Bool]]])
#     # raise Exception(f"Unknown type '{type(left)}', expected 'Bool' or 'Collection[Bool]'")

 # FIXME add test
 # Will this work? (since Implies1 has Collection[BB] as the type of its first arg, but BB for its second?)
 #   If it does work, will it also match when left : BB but right : Collection[BB] ? (expecting no)
@Implies1.instance(delegate = Collection_Bool)
# @Implies1.instance(delegate = (_Collection_Bool, BB)) # <<< or do I need to make a custom product type like this?
# @Implies1.instance(object)
def _Implies1_object(left: Collection[BB], right: BB) -> BB:
  if isinstance(left, Collection):
    if    ( len(get_args(left)) > 0 and Bool != get_args(left)[0] ) \
       or ( len(         left)  > 0 and type(peek(left)) not in get_args(Bool) ):
      raise mk_Boolean_TypeParameterError(left, Bool)
      # raise Exception(f"left is a collection but not of Bool = `{Bool}`:\nleft = '{left}'")
    return Implies(And1(left), right)
  else:
    raise mk_UnknownTypeError(left, [Collection[Bool]])

# @overload
# def Iff(left: BB, right: BB) -> BB: ...
# @overload
# def Iff(left: Collection[BB]) -> BB: ...
@typeclass(Boolean)
def Iff(left: BB, right: BB) -> BB: ...
# def Iff(left: Union[BB, Collection[BB]], right: Optional[BB]) -> BB: ...
@typeclass(Boolean)
def Iff1(bs: Collection[BB]) -> BB: ...

# @Iff.instance(delegate = _Collection_Bool)
@Iff.instance(object)
def _Iff_object(left: BB, right: BB) -> BB:
  if type(left) not in get_args(Bool):
    raise mk_UnknownTypeError(left, [Bool])
  elif type(right) not in get_args(Bool):
    raise mk_UnknownTypeError(right, [Bool])
  else:
    return And( Implies(left , right)
              , Implies(right, left )
              )

# def _Iff_object(left: Union[BB, Collection[BB]], right: Optional[BB]) -> BB:
#   if type(left) in get_args(Bool):
#     return And( Implies(left , right)
#               , Implies(right, left )
#               )
#   elif isinstance(left, Collection):
#     if    ( len(get_args(left)) > 0 and Bool != get_args(left)[0] ) \
#        or ( len(         left)  > 0 and type(peek(left)) not in get_args(Bool) ):
#       raise mk_Boolean_TypeParameterError(left, Bool)
#       # raise Exception(f"left is a collection but not of Bool = `{Bool}`:\nleft = '{left}'")
#     if right is not None:
#       raise mk_Boolean_OverloadingError(left, right)
#       # raise Exception("left is a collection but right is not None:\nleft = '{left}'\nright = '{right}'")
#     return Iff1(left)
#   else:
#     raise mk_UnknownTypeError(left, [Union[Bool, Collection[Bool]]])

@Iff1.instance(delegate = Collection_Bool)
# @Iff1.instance(object)
def _Iff1_object(bs: Collection[BB]) -> BB:
  if isinstance(bs, Collection):
    if    ( len(get_args(bs)) > 0 and Bool != get_args(bs)[0] ) \
       or ( len(         bs)  > 0 and type(peek(bs)) not in get_args(Bool) ):
      raise mk_Boolean_TypeParameterError(bs, Bool)
      # raise Exception(f"bs is a collection but not of Bool = `{Bool}`:\nbs = '{bs}'")
    b_peek = peek(bs)
    return And1([b == b_peek for b in bs])
  else:
    raise mk_UnknownTypeError(bs, [Collection[Bool]])


#############
# INSTANCES #
#############

##################################
# `bool` instances for `Boolean` #
##################################

# @Not.instance(delegate = _Collection_bool)
@Not.instance(bool)
def _Not_bool(b: bool) -> bool:
  return not b
  # if type(b) == bool:
  #   return not b
  # else:
  #   raise mk_UnknownTypeError(b, [bool])

# def _Not_bool(b: Union[bool, Collection[bool]]) -> bool:
#   if type(b) == bool:
#     return not b
#   elif isinstance(b, Collection):
#     if    ( len(get_args(b)) > 0 and bool != get_args(b)[0] ) \
#        or ( len(         b)  > 0 and type(peek(b)) != bool ):
#       raise mk_Boolean_TypeParameterError(b, bool)
#       # raise Exception(f"b is a collection but not of type bool = `{bool}`:\nb = '{b}")
#     return Not1(b)
#   else:
#     raise mk_UnknownTypeError(b, [Union[bool, Collection[bool]]])

# @Not1.instance(delegate = _Collection_bool)
# # @Not1.instance(bool)
# def _Not1_bool(bs: Collection[bool]) -> bool:
#   if isinstance(bs, Collection):
#     if    ( len(get_args(bs)) > 0 and bool != get_args(bs)[0] ) \
#        or ( len(         bs)  > 0 and type(peek(bs)) != bool ):
#       raise mk_Boolean_TypeParameterError(bs, bool)
#       # raise Exception(f"bs is a collection but not of type bool = `{bool}`:\nb = '{bs}")
#     return Not1(bs)
# #   return _Not_bool(_Or1_bool(bs))
#   else:
#     raise mk_UnknownTypeError(bs, [Collection[bool]])

# multi-arity arguments... CONTINUATION
#  - check overloaded examples in docs
#  search issues for "variadic" or "arity" or "multiple signatures" etc or "overloaded"
#    -https://github.com/dry-python/classes/issues/279
@And.instance(bool)
def _And_bool(left: bool, right: bool) -> bool:
  return left and right
  # if type(left) != bool:
  #   raise mk_UnknownTypeError(left, [bool])
  # elif type(right) not in get_args(Bool):
  #   raise mk_UnknownTypeError(right, [Bool])
  # else:
  #   return left and right

# @And.instance(delegate = _Collection_bool)
# @And.instance(bool)
# def _And_bool(left: Union[bool, Collection[bool]], right: Optional[bool]) -> bool:
#   if type(left) == bool:
#     if right is None:
#       raise mk_Boolean_OverloadingError1(bool)
#       # raise Exception("left is a bool but right is None")
#     else:
#       return left and right
#   elif isinstance(left, Collection):
#     if    ( len(get_args(left)) > 0 and bool != get_args(left)[0] ) \
#        or ( len(         left)  > 0 and type(peek(left)) != bool ):
#       raise mk_Boolean_TypeParameterError(left, bool)
#       # raise Exception(f"left is a collection but not of bool = `{bool}`:\nleft = '{left}'")
#     if right is not None:
#       raise mk_Boolean_OverloadingError(left, right)
#       # raise Exception("left is a collection but right is not None:\nleft = '{left}'\nright = '{right}")
#     return _And1_bool(left)
#   else:
#     raise mk_UnknownTypeError(left, [Union[bool, Collection[bool]]])


@And1.instance(delegate = Collection_bool)
# @And1.instance(bool)
def _And1_bool(bs: Collection[bool]) -> bool:
  return all_Bool(bs)
  # if isinstance(bs, Collection):
  #   if    ( len(get_args(bs)) > 0 and bool != get_args(bs)[0] ) \
  #      or ( len(         bs)  > 0 and type(peek(bs)) != bool ):
  #     raise mk_Boolean_TypeParameterError(bs, bool)
  #     # raise Exception(f"bs is a collection but not of bool = `{bool}`:\nleft = '{bs}'")
  #   return all_Bool(bs)
  # else:
  #   raise mk_UnknownTypeError(bs, [Collection[bool]])


@Or.instance(bool)
def _Or_bool(left: bool, right: bool) -> bool:
  return left or right
  # if type(left) != bool:
  #   raise mk_UnknownTypeError(left, [bool])
  # elif type(right) not in get_args(Bool):
  #   raise mk_UnknownTypeError(right, [Bool])
  # else:
  #   return left or right

# @Or.instance(delegate = _Collection_bool)
# @Or.instance(bool)
# def _Or_bool(left: Union[bool, Collection[bool]], right: Optional[bool]) -> bool:
#   if type(left) == bool:
#     if right is None:
#       raise mk_Boolean_OverloadingError1(bool)
#       # raise Exception("left is a bool but right is None")
#     return left or right
#   elif isinstance(left, Collection):
#     if    ( len(get_args(left)) > 0 and bool != get_args(left)[0] ) \
#        or ( len(         left)  > 0 and type(peek(left)) != bool ):
#       raise mk_Boolean_TypeParameterError(left, bool)
#       # raise Exception(f"left is a collection but not of Bool = `{Bool}`:\nleft = '{left}'")
#     if right is not None:
#       raise mk_Boolean_OverloadingError(left, right)
#       # raise Exception("left is a collection but right is not None:\nleft = '{left}'\nright = '{right}")
#     return _Or1_bool(left)
#   else:
#     raise mk_UnknownTypeError(left, [Union[bool, Collection[bool]]])

@Or1.instance(delegate = Collection_bool)
# @Or1.instance(bool)
def _Or1_bool(bs: Collection[bool]) -> bool:
  return any_Bool(bs)
  # if isinstance(bs, Collection):
  #   if    ( len(get_args(bs)) > 0 and bool != get_args(bs)[0] ) \
  #      or ( len(         bs)  > 0 and type(peek(bs)) != bool ):
  #     raise mk_Boolean_TypeParameterError(bs, bool)
  #     # raise Exception(f"bs is a collection but not of bool = `{bool}`:\nleft = '{bs}'")
  #   return any_Bool(bs)
  # else:
  #   raise mk_UnknownTypeError(bs, [Collection[bool]])

# @Implies.instance(bool)
# def _Implies_bool(left: Union[bool, Collection[bool]], right: bool) -> bool:
#   return #FIXME

# @Iff.instance(bool)
# def _Iff_bool(left: Union[bool, Collection[bool]], right: Optional[bool]) -> bool:
#   return #FIXME
# @Iff1.instance(bool)
# def _Iff1_bool(bs: Collection[bool]) -> bool:
#   return #FIXME



#####################################
# `bool` instances for `z3.BoolRef` #
#####################################

@Not.instance(z3.BoolRef)
def _Not_BoolRef(b: z3.BoolRef) -> z3.BoolRef:
  return z3.Not(b)
  # if type(b) == z3.BoolRef:
  #   return z3.Not(b)
  # else:
  #   raise mk_UnknownTypeError(b, [z3.BoolRef])

# @Not1.instance(delegate = _Collection_BoolRef)
# # @Not1.instance(z3.BoolRef)
# def _Not1_BoolRef(bs: Collection[z3.BoolRef]) -> z3.BoolRef:
#   if isinstance(bs, Collection):
#     if    ( len(get_args(bs)) > 0 and z3.BoolRef != get_args(bs)[0] ) \
#        or ( len(         bs)  > 0 and type(peek(bs)) != z3.BoolRef ):
#       raise mk_Boolean_TypeParameterError(bs, z3.BoolRef)
#       # raise Exception(f"bs is a collection but not of type z3.BoolRef = `{z3.BoolRef}`:\nb = '{bs}")
#     return Not1(bs)
# #   return _Not_bool(_Or1_bool(bs))
#   else:
#     raise mk_UnknownTypeError(bs, [Collection[z3.BoolRef]])


# @Not.instance(delegate = _Collection_BoolRef)
# @Not.instance(z3.BoolRef)
# def _Not_BoolRef(b: Union[z3.BoolRef, Collection[z3.BoolRef]]) -> z3.BoolRef:
#   if type(b) == z3.BoolRef:
#     return z3.Not( b )
#   elif isinstance(b, Collection):
#     if    ( len(get_args(b)) > 0 and z3.BoolRef != get_args(b)[0] ) \
#        or ( len(         b)  > 0 and type(peek(b)) != z3.BoolRef ):
#       raise mk_Boolean_TypeParameterError(b, z3.BoolRef)
#       # raise Exception(f"b is a collection but not of z3.BoolRef = `{z3.BoolRef}`:\nb = '{b}'")
#     return Not1(b)
#   else:
#     raise mk_UnknownTypeError(b, [Union[z3.BoolRef, Collection[z3.BoolRef]]])
# # @Not1.instance(z3.BoolRef)
# # def _Not1_bool(bs: Collection[bool]) -> z3.BoolRef:
# #   return _Not_bool(_Or1_bool(bs))

@And.instance(z3.BoolRef)
def _And_BoolRef(left: z3.BoolRef, right: z3.BoolRef) -> z3.BoolRef:
  return z3.And( left , right )
  # if type(left) != z3.BoolRef:
  #   raise mk_UnknownTypeError(left, [z3.BoolRef])
  # elif type(right) not in get_args(Bool):
  #   raise mk_UnknownTypeError(right, [Bool])
  # else:
  #   return z3.And( left , right )

@And1.instance(delegate = Collection_BoolRef)
# @And1.instance(z3.BoolRef)
def _And1_BoolRef(bs: Collection[z3.BoolRef]) -> z3.BoolRef:
  return z3.And(bs)
  # if isinstance(bs, Collection):
  #   if    ( len(get_args(bs)) > 0 and z3.BoolRef != get_args(bs)[0] ) \
  #      or ( len(         bs)  > 0 and type(peek(bs)) != z3.BoolRef ):
  #     raise mk_Boolean_TypeParameterError(bs, z3.BoolRef)
  #     # raise Exception(f"bs is a collection but not of z3.BoolRef = `{z3.BoolRef}`:\nleft = '{bs}'")
  #   return z3.And(bs)
  # else:
  #   raise mk_UnknownTypeError(bs, [Collection[z3.BoolRef]])

# @And.instance(delegate = _Collection_BoolRef)
# @And.instance(z3.BoolRef)
# def _And_BoolRef(left: Union[z3.BoolRef, Collection[z3.BoolRef]], right: Optional[z3.BoolRef]) -> z3.BoolRef:
#   if type(left) == z3.BoolRef:
#     if right is None:
#       raise mk_Boolean_OverloadingError1(z3.BoolRef)
#       # raise Exception("left is a z3.BoolRef but right is None")
#     else:
#       return z3.And( left , right )
#   elif isinstance(left, Collection):
#     if    ( len(get_args(left)) > 0 and z3.BoolRef != get_args(left)[0] ) \
#        or ( len(         left)  > 0 and type(peek(left)) != z3.BoolRef ):
#       raise mk_Boolean_TypeParameterError(left, z3.BoolRef)
#       # raise Exception(f"left is a collection but not of z3.BoolRef = `{z3.BoolRef}`:\nleft = '{left}'")
#     if right is not None:
#       raise mk_Boolean_OverloadingError(left, right)
#       # raise Exception("left is a collection but right is not None:\nleft = '{left}'\nright = '{right}")
#     else:
#       return _And1_bool(left)
#   else:
#     raise mk_UnknownTypeError(left, [Union[z3.BoolRef, Collection[z3.BoolRef]]])

# @And1.instance(delegate = _Collection_BoolRef)
# # @And1.instance(z3.BoolRef) #comment out? #FIXME
# def _And1_BoolRef(bs: Collection[z3.BoolRef]) -> z3.BoolRef:
#   return z3.And(bs)


@Or.instance(z3.BoolRef)
def _Or_BoolRef(left: z3.BoolRef, right: z3.BoolRef) -> z3.BoolRef:
  return z3.Or( left , right )
  # if type(left) != z3.BoolRef:
  #   raise mk_UnknownTypeError(left, [z3.BoolRef])
  # elif type(right) not in get_args(Bool):
  #   raise mk_UnknownTypeError(right, [Bool])
  # else:
  #   return z3.Or( left , right )

@Or1.instance(delegate = Collection_BoolRef)
# @Or1.instance(z3.BoolRef)
def _Or1_BoolRef(bs: Collection[z3.BoolRef]) -> z3.BoolRef:
  return z3.Or( bs )
  # if isinstance(bs, Collection):
  #   if    ( len(get_args(bs)) > 0 and z3.BoolRef != get_args(bs)[0] ) \
  #      or ( len(         bs)  > 0 and type(peek(bs)) != z3.BoolRef ):
  #     raise mk_Boolean_TypeParameterError(bs, z3.BoolRef)
  #     # raise Exception(f"bs is a collection but not of z3.BoolRef = `{z3.BoolRef}`:\nleft = '{bs}'")
  #   return z3.Or( bs )
  # else:
  #   raise mk_UnknownTypeError(bs, [Collection[z3.BoolRef]])

# @Or.instance(delegate = _Collection_BoolRef)
# @Or.instance(z3.BoolRef)
# def _Or_BoolRef(left: Union[z3.BoolRef, Collection[z3.BoolRef]], right: Optional[z3.BoolRef]) -> z3.BoolRef:
#   if type(left) == z3.BoolRef:
#     if right is None:
#       raise mk_Boolean_OverloadingError1(z3.BoolRef)
#       # raise Exception("left is a z3.BoolRef but right is None")
#     else:
#       return z3.Or( left , right )
#   elif isinstance(left, Collection):
#     if    ( len(get_args(left)) > 0 and z3.BoolRef != get_args(left)[0] ) \
#        or ( len(         left)  > 0 and type(peek(left)) != z3.BoolRef ):
#       raise mk_Boolean_TypeParameterError(left, z3.BoolRef)
#       # raise Exception(f"left is a collection but not of z3.BoolRef = `{z3.BoolRef}`:\nleft = '{left}'")
#     if right is not None:
#       raise mk_Boolean_OverloadingError(left, right)
#       # raise Exception("left is a collection but right is not None:\nleft = '{left}'\nright = '{right}")
#     else:
#       return _Or1_bool(left)
#   else:
#     raise mk_UnknownTypeError(left, [Union[z3.BoolRef, Collection[z3.BoolRef]]])

# @Or1.instance(delegate = _Collection_BoolRef)
# # @Or1.instance(z3.BoolRef)
# def _Or1_BoolRef(bs: Collection[z3.BoolRef]) -> z3.BoolRef:
#   return z3.Or(bs)


@Implies.instance(z3.BoolRef)
def _Implies_BoolRef(left: z3.BoolRef, right: z3.BoolRef) -> z3.BoolRef:
  return z3.Implies(left, right)
  # if type(left) != z3.BoolRef:
  #   raise mk_UnknownTypeError(left, [z3.BoolRef])
  # elif type(right) not in get_args(Bool):
  #   raise mk_UnknownTypeError(right, [Bool])
  # else:
  #   return z3.Implies(left, right)


# @Implies.instance(delegate = _Collection_BoolRef)
# @Implies.instance(z3.BoolRef)
# def _Implies_BoolRef(left: Union[z3.BoolRef, Collection[z3.BoolRef]], right: z3.BoolRef) -> z3.BoolRef:
#   if type(left) == z3.BoolRef:
#     return z3.Implies(left, right)
#   elif isinstance(left, Collection):
#     if    ( len(get_args(left)) > 0 and z3.BoolRef != get_args(left)[0] ) \
#        or ( len(         left)  > 0 and type(peek(left)) != z3.BoolRef ):
#       raise mk_Boolean_TypeParameterError(left, z3.BoolRef)
#       # raise Exception(f"left is a collection but not of z3.BoolRef = `{z3.BoolRef}`:\nleft = '{left}'")
#     return Implies1(left, right)
#   else:
#     raise mk_UnknownTypeError(left, [Union[z3.BoolRef, Collection[z3.BoolRef]]])

# @Iff.instance(z3.BoolRef)
# def _Iff_bool(left: Union[z3.BoolRef, Collection[z3.BoolRef]], right: Optional[Bool]) -> z3.BoolRef:
#   return #FIXME
# @Iff1.instance(z3.BoolRef)
# def _Iff1_bool(bs: Collection[Bool]) -> z3.BoolRef:
#   return #FIXME
