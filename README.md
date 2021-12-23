# ExImp
Various experiments on the Imp.

For now all code are from FRAP, except for `MyIMP.v`.
The original readme is [here](./README-frap.md).

# Usage
Just `make` and then open `MyImp.v` with coqide or proof general.

# Progress
Current: CPS & compilation correctness

TODO:
* Hoare logic and its automation
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
