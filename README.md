
# Evidence-providing problem solvers in Agda

[PDF](https://umazalakain.info/static/report.pdf)

The report, including all software written for it, is in the `report` directory.
It can be compiled into PDF by running `make`. Note that for this to succeed,
all literate Agda files need to be compiled. These were written for Agda 2.5.3
and depend on the standard library. To just compile the Agda modules on which
the report depends, run `make modules`.

The reports uses the TeX package `catchfilebetweentags` to include parts of
the literate Agda modules, which contain the following:

- `Monoids`: a complete solver for equations on monoids.
- `CommutativeRings`: the solver for equations on commutative rings from Agda's
  standard library.
- `Normalisation`: unverified normalisation of Presburger formulae.
- `Presburger`: the Omega Test for Presburger arithmetic, verified but
  unfinished.
- `Adaptation`: a small wrapper around `Presburger` and `Normalisation` allowing
  a limited usage case.
- `Demo`: a showcase of `Monoids`, `CommutativeRings` and `Adaptation`.
