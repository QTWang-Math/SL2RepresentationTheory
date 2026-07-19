/-
Copyright (c) 2026 LieTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LieTheory contributors
-/
import LieTheory.SL2RHarishChandra.Casimir
import Mathlib.LinearAlgebra.Finsupp.Span

/-!
# Algebraic Harish--Chandra modules for `SL₂(ℝ)`

This file is deliberately specialized to the Harish--Chandra pair
`(sl₂(ℂ), SO(2))`.  The `SO(2)`-finite action is represented by an algebraic
direct sum of the integral eigenspaces of the fixed element `H`.
-/

namespace LieTheory.SL2RHarishChandra

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
variable [LieRingModule sl2Compact M] [LieModule ℂ sl2Compact M]

/-- Every vector is an algebraic finite sum of integral `SO(2)` weights. -/
def IsKFinite : Prop := ⨆ n : ℤ, KWeightSpace M n = ⊤

/-- Every integral K-type is finite-dimensional. -/
def IsAdmissible : Prop := ∀ n : ℤ, Module.Finite ℂ (KWeightSpace M n)

/-- The algebraic `SL₂(ℝ)` Harish--Chandra module conditions. -/
structure IsHarishChandraModule : Prop where
  kFinite : IsKFinite M
  admissible : IsAdmissible M

/-- The set of integral weights occurring in this fixed `SL₂(ℝ)` module. -/
def KSupport : Set ℤ := {n | KWeightSpace M n ≠ ⊥}

theorem isKFinite_iff_forall_exists_finset :
    IsKFinite M ↔
      ∀ v : M, ∃ s : Finset ℤ, v ∈ ⨆ n ∈ s, KWeightSpace M n := by
  constructor
  · intro h v
    apply Submodule.mem_iSup_iff_exists_finset.mp
    rw [h]
    exact Submodule.mem_top
  · intro h
    apply top_unique
    intro v _
    exact Submodule.mem_iSup_iff_exists_finset.mpr (h v)

theorem kWeightSpaces_iSupIndep : iSupIndep (KWeightSpace M) := by
  exact (HAction M).eigenspaces_iSupIndep.comp (Int.cast_injective :
    Function.Injective (fun n : ℤ => (n : ℂ)))

end LieTheory.SL2RHarishChandra
