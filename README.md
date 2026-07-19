# SL2RepresentationTheory

A Lean 4 + mathlib project for formalizing Lie theory.

## Layout

- `Main.lean`: executable smoke tests for algebra, groups, rings, and matrix Lie algebras.
- `SL2RepresentationTheory.lean`: root module of the reusable library.
- `SL2RepresentationTheory/Basic.lean`: initial reusable Lie algebra definitions.
- `SL2RepresentationTheory/Sl2Classification/Basic.lean`: generating-triple hypothesis and API imports.
- `SL2RepresentationTheory/Sl2Classification/HighestWeight.lean`: primitive vectors and `sl₂` string formulas.
- `SL2RepresentationTheory/Sl2Classification/StringBasis.lean`: linear independence, invariant span, basis, dimension, and uniqueness.
- `SL2RepresentationTheory/Sl2Classification/Classification.lean`: public highest-weight classification theorem.
- `SL2RepresentationTheory/SL2RHarishChandra/CompactBasis.lean`: the compact `H,E,F` basis of `sl₂(ℂ)`.
- `SL2RepresentationTheory/SL2RHarishChandra/Casimir.lean`: the normalization
  `C = H² + 2H + 4FE` and its centrality and weight formulas.
- `SL2RepresentationTheory/SL2RHarishChandra/HarishChandraModule.lean`: the specialized
  algebraic K-finite/admissible model for `(sl₂(ℂ), SO(2))`.
- `SL2RepresentationTheory/SL2RHarishChandra/Models.lean`: the four explicit Finsupp models.
- `SL2RepresentationTheory/SL2RHarishChandra/Irreducibility.lean`: irreducibility of all four models.
- `SL2RepresentationTheory/SL2RHarishChandra/Classification.lean`: barrier and seed-vector classification.
- `SL2RepresentationTheory/SL2RHarishChandra/ModelEquivalences.lean`: explicit model maps and Lie-module equivalences.
- `SL2RepresentationTheory/SL2RHarishChandra/FinalClassification.lean`: uniqueness, multiplicity one,
  support classification, and the final four-class theorem.
- `lakefile.toml`: Lake package, mathlib dependency, library, and executable targets.
- `lean-toolchain`: exact Lean toolchain used by both Lake and the VSCode extension.

## Commands

```sh
lake update
lake build
lake exe Main
```

Open this directory (the one containing `lakefile.toml`) in VSCode and install
the recommended **Lean 4** extension when prompted.

## `sl₂` classification status

The theorem `finiteDimensional_irreducible_classification` proves, without
additional axioms or unfinished proofs, that a finite-dimensional irreducible
module for a generating `sl₂` triple has a unique natural-number highest
weight and a basis satisfying the standard `h`, `e`, and `f` action formulas.

An independently constructed `StandardModule n`, its irreducibility, and a
packaged `LieModuleEquiv` are not yet part of this project. Mathlib v4.32.0 does
not currently provide the needed standard representation or symmetric-power
Lie-module construction, so those remain a separate future development.

## `SL₂(ℝ)` Harish--Chandra classification status

The theorem `classify_irreducible_harishChandra_rho` proves that every
nonzero irreducible admissible algebraic Harish--Chandra module for
`(sl₂(ℂ), SO(2))`, with Casimir `C = H² + 2H + 4FE` acting by zero, is
Lie-module equivalent to exactly one of:

- the trivial module;
- the positive algebraic discrete-series module;
- the negative algebraic discrete-series module;
- the odd algebraic principal-series module.

The development also proves `kType_multiplicity_one` and `classify_KSupport`.
It uses only algebraic direct sums (`Finsupp`); no globalization, topology,
unitarity, Haar measure, Hilbert space, or analytic induction is formalized.
