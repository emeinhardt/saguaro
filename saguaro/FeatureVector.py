'''
Module for feature vectors.
'''

from dataclasses import dataclass
# from collections.abc import Collection#, Mapping, Sequence
from typing import TypeVar#, Optional, Union, Callable,
from typing import Collection, Sequence, FrozenSet, Set, Tuple, List
from classes import AssociatedType, Supports, typeclass
# from abc import ABCMeta, abstractmethod

import hypothesis
# from hypothesis import ???
from hypothesis import strategies as st

import z3

# from saguaro.utilities import ???
from saguaro._Boolean import Bool #\
                           # , Not, Not1 \
                           # , And, And1 \
                           # , Or, Or1 \
                           # , Implies, Implies1 \
                           # , Iff, Iff1
from saguaro.Eq import Eq, eq, neq, distinct, eq1
# from saguaro.Order import EquivalenceRelation
from saguaro.Order import Preorder, PartialOrder, LowerBounded, UpperBounded \
                        , MeetSemilattice, JoinSemilattice \
                        # , BoundedMeetSemilattice, BoundedJoinSemilattice \
                        # , Lattice \
                        # , BoundedLattice \
                        # , ComplementedLattice \
                        # , HasOrthocomplementInvolution \
                        # , Orthocomplemented \
                        # , DistributiveLattice \
                        # , Nearlattice \
                        # , BooleanLattice \
# from saguaro.Order import ???
# from saguaro.Subset import ???


class FeatureVector(AssociatedType): ...

FV = TypeVar("FV", bound=Supports[FeatureVector])

@typeclass(FeatureVector)
def __len__():
    pass
