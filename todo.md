# TODO

## Major feature map

Main goals: support feature vector research + prototype different encodings in `z3`.

1. Tested typeclass implementations for at least one concrete and one symbolic implementation of 
  a. some encoding of sets/subsets/powersets.
  b. some encoding of feature vectors.
  c. some encoding of rewrite rules.
2. Visualization support
 - Allow export of collections defining a preorder as `gml` or `graphml` files for rendering.
 - Allow export of `z3` Boolean expressions/ASTs for debugging/exposition.
3. Light(er)weight alternative build/install options:
 - `conda` instructions for pure-Python dependencies.
 - `z3` build/install instructions.
4. Support for importing/exporting concrete feature systems.

## Development todo scratch
 - Map.py
    - any subset of the free functional nearlattice is a boolean nearlattice (Cirulis 2015, p. 4 in passing)
        - any functional nearlattice where all pairwise unions of elements are also elements is `closed`
    - alternative / easier to test for def of overriding given by lemma 2.7 ('(5)', cf. '(6)') of Cirulis 2011
    - prop 6.1 of Cirulis 2011 has a def of subtraction in Boolean nearlattices
    - prop 6.2 of Cirulis 2011 has a set of Boolean nearlattice properties
    - lemma 6.3 of Cirulis 2011 has a set of Boolean o-nearlattice properties
 - Order.py
   - Tech debt:
    - clean up the assertions in the else branches on stuff with the Optional[Ps] arg
    - make top and bot elements generatable for symbolic vectors
    - allow top, bot elements to be passed in
    - Finish placement/implementation of the following functions/relations: 
     - `upper closure` and `lower closure`
     - `is_antichain` / `is_descending_chain` / `is_ascending_chain`
 - Pending progress in FS/FV, figure out where to place requirements for interface functions that do direct calculation (i.e. `meet` compared to `is_meet`)
 - Subset.py
   - SymbolicBoolVector implementation


