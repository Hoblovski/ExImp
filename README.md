# ExImp
Various experiments on the Imp.

For now all code are from FRAP, except for `MyIMP.v`, whose code is written by me.
> Actually I do not use much from FRAP except for very few tactics and transition systems.
> So this could be a standalone file.
The original readme is [here](./README-frap.md).

# Usage
Just `make` and then open `MyImp.v` with coqide or proof general.

# Contents
* Deep embedded IMP language
* Natural semantics
* Small-step semantics
* CPS style small semantics
* Equivalence proof between three semantics
* Hoare logic for IMP and its soundness proof

* A stack machine and its semantics
* Compiling IMP to the stack machine
* Compiler correctness via simulation argument

# Progress
TODO:
* Hoare logic automation
* Separation logic
* Concurrency and Rely guarantee
* Various other logics
* Compiling to register-based than stack-based machine
* Techniques in compcert: ad-hoc validation...

Meant to be a mini-compcert.

# References
* Software foundations
  - Introduction to coq
* Certified programming with dependent types
  - Automated tricks
* Formal reasoning about programs
  - Program verification
  - My Code is base on it.
* CompilerVerif
  - Xavier Levoy
  - Inspires me about CPS.

# LICENSE
Same as FRAP.
