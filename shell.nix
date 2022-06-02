{ pkgs ? import (fetchTarball https://github.com/NixOS/nixpkgs/archive/nixos-unstable.tar.gz) {
  config = { allowBroken = false; };
} }:

let
  mach-nix = import (builtins.fetchGit {
    url = "https://github.com/DavHau/mach-nix";
    ref = "refs/tags/3.4.0";
  }) {
    # optionally set python version here
    # python = "python39";

    # optionally update pypi data revision from https://github.com/DavHau/pypi-deps-db
    pypiDataRev = "3d8c7476384ec140af45efa7608f412923a3ff3d";
    # pypiDataSha256 = <final output line of
    # `nix-prefetch-url --unpack "https://github.com/DavHau/pypi-deps-db/archive/3d8c7476384ec140af45efa7608f412923a3ff3d.zip"`
    # >
    pypiDataSha256 = "1w2mihwwrxy0c4nwcn8l152n7b4r20h4r9lbvjlig7bffvs5vwaz";
  };

  python-custom = mach-nix.mkPython rec {
    python = "python39";
    requirements = builtins.readFile ./requirements.txt;

    #packageextra + a local download of the wheel from pypi is an alternative option to updating the comprehensive python package distribution DavHau maintains
  #   packagesExtra = [
  #     (mach-nix.buildPythonPackage {
  #       pname = "cvc5";
  #       version = "1.0.0";
  #       format = "wheel";
  #       src = ./cvc5-1.0.0-cp39-cp39-manylinux_2_17_x86_64.manylinux2014_x86_64.whl;
  #       requirements = ''
  #         Cython
  #         scikit-build
  #         pytest
  #       '';
  #       }
  #     )
  #   ];

    # packagesExtra = p : [
    #   p.mypy
    #   p.python39Packages.python-lsp-server
    #   p.python39Packages.pytest
    #   p.python39Packages.mypy
    #   p.python39Packages.pytest-mypy
    # ];
  };

  jupyter = import (builtins.fetchGit {
    url = https://github.com/tweag/jupyterWith;
    rev = "f64a2fd6a7b0cff8b3cb874641bef3ebd96d680f"; #e80d490476856d36405950fb64cf393d599fe246
    # ref = "master";
  }) {};

  bash = jupyter.kernels.bashKernel {
    name = "bash";
  };

  iPython = jupyter.kernels.iPythonWith {
    name = "mach-nix-saguaro";
    ignoreCollisions = true;
    #python3 = pkgs.python3Packages;
    python3 = python-custom.python;
    packages = python-custom.python.pkgs.selectPkgs;
  };

#  iHaskell = jupyter.kernels.iHaskellWith {
#    name = "haskell";
#    packages = p: with p; [ 
#      formatting 
#      doctest
#      # QuickCheck
#      hashable
#      containers
#      unordered-containers
#      split
#      fin
#      vec
#      type-level-sets
#      tfp
#      boomerang
#      text 
#      ipa
#      indexed
#      indexed-profunctors
#      parameterized-utils
#      comonad
#      comonad-extras
#      folds
#      nonempty-containers 
#      nonempty-zipper
#      nonempty-vector
#      zippers
#      # list-zipper # 'broken'?
#      profunctors
#      ## coapplicative # doesn't even exist on hackage??
#      ## newtype-generics
#      # profunctor-optics # 'broken'?
#      lens
#      optics
#      # lens-tutorial # 'broken'?
#      sbv
#      z3
#      # z3cat
#      simple-smt
#      HaskellForMaths
#      lattices
#      partial-order
#      semilattices
#    ];
#    haskellPackages = pkgs.haskellPackages;
#  };

  jupyterEnvironment =
    jupyter.jupyterlabWith {
#      kernels = [ iPython iHaskell ];
      kernels = [ bash iPython ];
      directory = ./jupyterlab;
      # extraInputsFrom = p: [ ];
      extraPackages = p: [ 
        # ghc etc will not have access to the packages that iHaskell does...
#        p.ghc                     # 8.10.4
#        p.cabal-install
#        p.cabal2nix
#        p.stack
#        p.hlint                   # v3.3.1
#        p.ormolu                  # v0.1.4.1
#        p.stylish-haskell         # v0.12.2.0 
#        p.haskell-language-server # 1.1.0.0 (GHC 8.10.4)
#        p.agda                    # v2.6.1.3
#        p.agda-pkg
        p.z3
        p.cvc4
        #p.cvc5 # appears to be unnecessary to get cvc5 working in ipython (i.e. in a project shell) and within jupyter
        # python-custom
        #p.python38Full
        #p.boost
        #p.expat
        #p.cgal
        #p.sparsehash
        #p.gtk3
        #p.cairomm
        #p.graphviz
        #p.dot2tex
        #p.kgraphviewer
        #p.xdot
        # p.mypy
        # p.python39Packages.python-lsp-server
        # p.python39Packages.pytest
        # p.python39Packages.mypy
        # p.python39Packages.pytest-mypy
        #p.python39Packages.pyls-mypy
      ];
    };
in
pkgs.mkShell rec {
  buildInputs = [
    jupyterEnvironment
    iPython.runtimePackages
    # python-custom
    # python-custom.runtimePackages # does not exist
    #python-custom.env
    python-custom.python.pkgs."funcy"       # used
    python-custom.python.pkgs."expression"
    python-custom.python.pkgs."frozendict"
    python-custom.python.pkgs."bidict"
    python-custom.python.pkgs."immutables"
    python-custom.python.pkgs."toolz"
    # python-custom.python.pkgs."fn.py"     #original `fn` is unmaintained; active fork requires installation from source `https://github.com/fnpy/fn.py#installation`
    python-custom.python.pkgs."algebraic-data-types"
    python-custom.python.pkgs."classes"     # used
    python-custom.python.pkgs."returns"
    python-custom.python.pkgs."more-itertools" # used
    python-custom.python.pkgs."glom"
    python-custom.python.pkgs."pytest"      # used
    python-custom.python.pkgs."mypy"        # used
    python-custom.python.pkgs."pytest-mypy" # used
    python-custom.python.pkgs."pytest-mypy-plugins" # used
    python-custom.python.pkgs."mypy-extensions" # used
    python-custom.python.pkgs."phantom-types"
    python-custom.python.pkgs."beartype"
    python-custom.python.pkgs."python-lsp-server" # used
    python-custom.python.pkgs."hypothesis" # used
    python-custom.python.pkgs."z3-solver"  # used
    python-custom.python.pkgs."cvc5" # used / works
    python-custom.python.pkgs."pympler"
    python-custom.python.pkgs."tqdm"       # used
    pkgs.cvc5 # fine
  ];
  # ++ jupyterEnvironment.env.buildInputs
  # ++ python-custom.python.pkgs;
  # ++ python-custom.env.buildInputs;
  # ++ python-custom.python.pkgs.selectPkgs;

  PYTHON = "${python-custom}/bin/python";

  shellHook = ''
  '';
}
  # jupyterEnvironment.env
  #
  # pkgs.mkShell {
  #   name = "fresnel-shell";
  #   inputsFrom = p: [];
  #   buildInputs = [
  #     jupyterEnvironment.jupyterlab
  #     generateDirectory
  #     generateLockFile
  #     pkgs.nodejs
  #   ] ++ (map (k: k.runtimePackages) kernels)
  #   ++ ();
  # };
