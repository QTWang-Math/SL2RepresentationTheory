/-
Copyright (c) 2026 SL2RepresentationTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SL2RepresentationTheory contributors
-/
import SL2RepresentationTheory.SL2RHarishChandra.CompactBasis
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Integral `SO(2)` weights for algebraic `SL₂(ℝ)` modules

All definitions in this file are specialized to the fixed complexified Lie
algebra `sl2Compact`.  The integer grading is the algebraic replacement for
the `SO(2)`-finite action; no general theory of weights is introduced.
-/

namespace SL2RepresentationTheory.SL2RHarishChandra

open LieModule

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
variable [LieRingModule sl2Compact M] [LieModule ℂ sl2Compact M]

/-- The integer `SO(2)` K-type of weight `n` in an algebraic `SL₂(ℝ)` module. -/
def KWeightSpace (n : ℤ) : Submodule ℂ M :=
  (LieModule.toEnd ℂ sl2Compact M H).eigenspace (n : ℂ)

theorem mem_KWeightSpace_iff {n : ℤ} {v : M} :
    v ∈ KWeightSpace M n ↔ ⁅H, v⁆ = (n : ℂ) • v := by
  rw [KWeightSpace, Module.End.mem_eigenspace_iff]
  rfl

/-- `E` raises an integral K-weight by two. -/
theorem E_mem_KWeightSpace {n : ℤ} {v : M} (hv : v ∈ KWeightSpace M n) :
    ⁅E, v⁆ ∈ KWeightSpace M (n + 2) := by
  rw [mem_KWeightSpace_iff] at hv ⊢
  rw [leibniz_lie, lie_H_E, hv]
  simp only [smul_lie, lie_smul]
  push_cast
  module

/-- `F` lowers an integral K-weight by two. -/
theorem F_mem_KWeightSpace {n : ℤ} {v : M} (hv : v ∈ KWeightSpace M n) :
    ⁅F, v⁆ ∈ KWeightSpace M (n - 2) := by
  rw [mem_KWeightSpace_iff] at hv ⊢
  rw [leibniz_lie, lie_H_F, hv]
  simp only [neg_lie, smul_lie, lie_smul]
  push_cast
  module

end SL2RepresentationTheory.SL2RHarishChandra
