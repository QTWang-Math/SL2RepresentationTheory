/-
Copyright (c) 2026 LieTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LieTheory contributors
-/
import LieTheory.Sl2Classification.StringBasis

/-!
# Classification of finite-dimensional irreducible `sl₂` modules

The main theorem states that a finite-dimensional irreducible module for a
generating `sl₂` triple has a unique natural-number highest weight and a basis
on which `h`, `e`, and `f` act by the standard formulas.

## Reused mathlib results

The proof uses `IsSl2Triple.exists_hasPrimitiveVectorWith` for existence of a
primitive vector and the four string results in
`IsSl2Triple.HasPrimitiveVectorWith`: `lie_h_pow_toEnd_f`,
`lie_e_pow_succ_toEnd_f`, `pow_toEnd_f_ne_zero_of_eq_nat`, and
`pow_toEnd_f_eq_zero_of_eq_nat`.
-/

namespace LieTheory.Sl2Classification

universe u v w

variable {K : Type u} {L : Type v} {M : Type w}
variable [Field K] [CharZero K] [IsAlgClosed K]
variable [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable [Nontrivial M] [FiniteDimensional K M] [LieModule.IsIrreducible K L M]
variable {h e f : L}

/-- Every nonzero finite-dimensional irreducible module for a generating
`sl₂` triple has a unique highest weight and a basis satisfying all standard
action formulas. -/
theorem finiteDimensional_irreducible_classification
    (t : IsSl2Triple h e f) (hgen : IsGenerating (K := K) t) :
    ∃! n : ℕ, HasHighestWeightBasis (K := K) (M := M) t n :=
  exists_unique_highestWeight_basis t hgen

end LieTheory.Sl2Classification
