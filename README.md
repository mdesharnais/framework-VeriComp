# Isabelle/HOL Framework for Verified Compilers

There are two ways to build the formalization: in debug and in build mode.

In debug mode, the option `quick_and_dirty` is set, which allows to use `sorry`
in proofs.

    $ make debug

In build mode, the use of `sorry` leads to an error and statements must have
complete proofs.

    $ make build

# Compatibility

Known to work with [Isabelle/HOL 2019](https://isabelle.in.tum.de/website-Isabelle2019/index.html).
