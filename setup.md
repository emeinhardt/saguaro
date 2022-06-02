
# Setup

This project uses `tweag`'s `jupyterWith` project to create a `nix`-managed JupyterLab repository.
For more about this project, see https://github.com/tweag/jupyterWith.

## Prerequisites

Code has currently only been developed and tested on Linux. Windows is not currently supported. WSL support is unknown.

This project uses the `nix` package manager to declare and manage dependencies. FIXME describe how to get `nix` (and any salient gotchas).

From personal experience, having `jupyter` globally installed (at least via `nix`) will prevent any extensions from being succesfully added.

## Steps 

1. Clone this repository and `cd` into it.
2. Setup jupyterlab extensions: `bash setup.sh` 
 - This creates a folder `jupyterlab` in the current directory.
 - It then launches a nix-shell instance and attempts to add the extensions itemized in `extensions.sh` and the packages listed in `shell.nix`.
   - It is normal for this to take several minutes the first time it is done. Any dependencies directly managed by `nix` (some of the Python dependencies are delegated by `mach-nix` to `pip` or `poetry`) will be intelligently cached. 
 - If you have no intention of using `jupyterLab`, you may skip `bash setup.sh` and just enter `nix-shell` in the root of this project in your shell.

# Use

## Starting a notebook server

1. `cd` into the repository.
2. `nix-shell --command "jupyter lab"`

Alternatively, install `direnv` and then in the root of this project's repository, enter `echo "use_nix" > .envrc && direnv allow` in your shell. When you `cd` into this directory, `direnv` will set up dependencies as you'd expect, and you can now launch `jupyter lab` without going into `nix-shell` first.

# Advanced setup / modification

## Jupyter Extensions

If you'd like to change the JupyterLab extensions that are available:

 1. Edit `extensions.sh`. Mind the hacky use of whitespace.
 2. You probably want to clear cached JupyterLab files:
   - While in the project directory, enter `rm -rf ./jupyterLab && rm -rf ./nbconvert` in your shell.
 3. Run `bash setup.sh` from the root of the project directory while in your shell.
   - Errors you see during `bash setup.sh` after adding extensions will probably relate to version constraint incompatibilities between the extension you want and the version of JupyterLab specified in this project.

## Python

If you'd like to modify the Python dependencies that are available, edit `requirements.txt` in the root of the repository.

Changing the version of the Python distribution might break the project or require a lot of work until one or more of `jupyterWith`, `IHaskell`, or `mach-nix` update things on their end.

## (I)Haskell packages

If you'd like to modify what Haskell packages are available in IHaskell, modify the list of packages specified in `shell.nix` in the `packages` argument to `iHaskell = jupyter.kernels.iHaskellWith {...}`.

Note that adding Haskell packages flagged as "broken" by Nix will result in a build error by default; many Haskell packages are flagged as broken because an automated build of them failed in a way that doesn't actually mean the package is broken (e.g. a dependency that's not declared in a way Nix understands may cause the build or tests to fail). There is a flag at the top of `shell.nix` to allow "broken" packages; it is set to `false` by default. 


## Other dependencies

All other dependencies are specified in the `extraPackages` argument of `jupyterEnvironment = jupyter.jupyterLabWith {...}` towards the bottom of `shell.nix`.

