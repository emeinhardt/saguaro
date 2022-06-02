# `lentic-skew`

This is a demonstration repository intended to show challenges and workflows of using synthesis for computational phonology.
The case study is big enough to be interesting --- reasoning about SPE-style feature vectors (inferring natural classes, inferring rewrite rule target and change vectors) --- and small enough to not be that challenging to embed into `z3`.

## Requirements

Dependencies are principally managed by the declarative, hash-store-based package manager [nix](https://nixos.org/download.html).

Once you have `nix` installed, and have cloned this repository to a local folder `.../<this-repository>`, follow the instructions in `setup.md`.
Note that first-time setup may take a while, and there may be a delay between the first `nix` command and visible console output: `nix` is finding a build derivation that fits your system, finding (if possible) pre-cached binaries, and a variety of other tasks.

### Checking if the installation succeeded:

You should be able to run `mypy` and/or `pytest` from the root directory of the repository.
