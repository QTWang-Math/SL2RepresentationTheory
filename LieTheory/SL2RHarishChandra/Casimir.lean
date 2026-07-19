/-
Copyright (c) 2026 LieTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LieTheory contributors
-/
import LieTheory.SL2RHarishChandra.KTypes
import Mathlib.Tactic.NoncommRing

/-!
# The rho-normalized Casimir for algebraic `SL₂(ℝ)` modules

For the fixed basis `H`, `E`, `F`, our convention is

`C = H² + 2H + 4FE = H² - 2H + 4EF`.

The phrase "infinitesimal character rho" means exactly that this operator acts
by zero.  This is the central character of the trivial representation in this
normalization.
-/

namespace LieTheory.SL2RHarishChandra

open LieModule

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
variable [LieRingModule sl2Compact M] [LieModule ℂ sl2Compact M]

local instance : LieRing (Module.End ℂ M) := LieRing.ofAssociativeRing

abbrev HAction : Module.End ℂ M := LieModule.toEnd ℂ sl2Compact M H
abbrev EAction : Module.End ℂ M := LieModule.toEnd ℂ sl2Compact M E
abbrev FAction : Module.End ℂ M := LieModule.toEnd ℂ sl2Compact M F

/-- The rho-normalized Casimir action `H² + 2H + 4FE`. -/
def casimirAction : Module.End ℂ M :=
  HAction M * HAction M + 2 • HAction M + 4 • (FAction M * EAction M)

/-- In our fixed normalization, infinitesimal character rho means that the
Casimir acts by zero. -/
def HasRhoInfinitesimalCharacter : Prop := casimirAction M = 0

theorem HAction_EAction_commutator :
    HAction M * EAction M - EAction M * HAction M = 2 • EAction M := by
  have h := LieHom.map_lie (LieModule.toEnd ℂ sl2Compact M) H E
  rw [lie_H_E] at h
  simpa [Ring.lie_def, two_smul] using h.symm

theorem HAction_FAction_commutator :
    HAction M * FAction M - FAction M * HAction M = -(2 • FAction M) := by
  have h := LieHom.map_lie (LieModule.toEnd ℂ sl2Compact M) H F
  rw [lie_H_F] at h
  simpa [Ring.lie_def, two_smul] using h.symm

theorem EAction_FAction_commutator :
    EAction M * FAction M - FAction M * EAction M = HAction M := by
  have h := LieHom.map_lie (LieModule.toEnd ℂ sl2Compact M) E F
  rw [lie_E_F] at h
  simpa [Ring.lie_def] using h.symm

theorem HAction_mul_EAction :
    HAction M * EAction M = 2 • EAction M + EAction M * HAction M :=
  sub_eq_iff_eq_add.mp (HAction_EAction_commutator M)

theorem EAction_mul_HAction :
    EAction M * HAction M = HAction M * EAction M - 2 • EAction M := by
  noncomm_ring [HAction_mul_EAction M]

theorem HAction_mul_FAction :
    HAction M * FAction M = -(2 • FAction M) + FAction M * HAction M :=
  sub_eq_iff_eq_add.mp (HAction_FAction_commutator M)

theorem FAction_mul_HAction :
    FAction M * HAction M = HAction M * FAction M + 2 • FAction M := by
  noncomm_ring [HAction_mul_FAction M]

theorem EAction_mul_FAction :
    EAction M * FAction M = HAction M + FAction M * EAction M :=
  sub_eq_iff_eq_add.mp (EAction_FAction_commutator M)

theorem FAction_mul_EAction :
    FAction M * EAction M = EAction M * FAction M - HAction M := by
  noncomm_ring [EAction_mul_FAction M]

private theorem FAction_HAction_EAction :
    FAction M * (HAction M * EAction M) =
      HAction M * (FAction M * EAction M) + 2 • (FAction M * EAction M) := by
  calc
    FAction M * (HAction M * EAction M) =
        (FAction M * HAction M) * EAction M := by rw [mul_assoc]
    _ = (HAction M * FAction M + 2 • FAction M) * EAction M := by
      rw [FAction_mul_HAction]
    _ = HAction M * (FAction M * EAction M) + 2 • (FAction M * EAction M) := by
      noncomm_ring

private theorem HAction_EAction_HAction :
    HAction M * (EAction M * HAction M) =
      EAction M * (HAction M * HAction M) + 2 • (EAction M * HAction M) := by
  calc
    HAction M * (EAction M * HAction M) =
        (HAction M * EAction M) * HAction M := by rw [mul_assoc]
    _ = (2 • EAction M + EAction M * HAction M) * HAction M := by
      rw [HAction_mul_EAction]
    _ = EAction M * (HAction M * HAction M) + 2 • (EAction M * HAction M) := by
      noncomm_ring

private theorem HAction_FAction_HAction :
    HAction M * (FAction M * HAction M) =
      FAction M * (HAction M * HAction M) - 2 • (FAction M * HAction M) := by
  calc
    HAction M * (FAction M * HAction M) =
        (HAction M * FAction M) * HAction M := by rw [mul_assoc]
    _ = (-(2 • FAction M) + FAction M * HAction M) * HAction M := by
      rw [HAction_mul_FAction]
    _ = FAction M * (HAction M * HAction M) - 2 • (FAction M * HAction M) := by
      noncomm_ring

/-- The second standard expression `H² - 2H + 4EF` for the same Casimir. -/
theorem casimirAction_eq_alternative :
    casimirAction M =
      HAction M * HAction M - 2 • HAction M + 4 • (EAction M * FAction M) := by
  unfold casimirAction
  noncomm_ring [EAction_mul_FAction M]

theorem casimirAction_commute_H : Commute (casimirAction M) (HAction M) := by
  change casimirAction M * HAction M = HAction M * casimirAction M
  unfold casimirAction
  noncomm_ring [EAction_mul_HAction M, HAction_mul_FAction M, FAction_HAction_EAction M]

theorem casimirAction_commute_E : Commute (casimirAction M) (EAction M) := by
  change casimirAction M * EAction M = EAction M * casimirAction M
  unfold casimirAction
  noncomm_ring [HAction_mul_EAction M, FAction_mul_EAction M, HAction_EAction_HAction M]

theorem casimirAction_commute_F : Commute (casimirAction M) (FAction M) := by
  change casimirAction M * FAction M = FAction M * casimirAction M
  unfold casimirAction
  noncomm_ring [HAction_mul_FAction M, EAction_mul_FAction M, HAction_FAction_HAction M]

theorem casimirAction_apply (v : M) :
    casimirAction M v =
      ⁅H, ⁅H, v⁆⁆ + 2 • ⁅H, v⁆ + 4 • ⁅F, ⁅E, v⁆⁆ := by
  simp [casimirAction, Module.End.mul_apply]

theorem casimirAction_alternative_apply (v : M) :
    casimirAction M v =
      ⁅H, ⁅H, v⁆⁆ - 2 • ⁅H, v⁆ + 4 • ⁅E, ⁅F, v⁆⁆ := by
  rw [casimirAction_eq_alternative]
  simp [Module.End.mul_apply]

/-- On K-weight `n`, the equation `C = 0` gives the denominator-free
composition formula for first raising and then lowering. -/
theorem rho_F_E_formula {n : ℤ} {v : M}
    (hrho : HasRhoInfinitesimalCharacter M) (hv : v ∈ KWeightSpace M n) :
    (4 : ℂ) • ⁅F, ⁅E, v⁆⁆ = -((n : ℂ) * ((n : ℂ) + 2)) • v := by
  have hc : casimirAction M v = 0 := by rw [hrho]; rfl
  rw [casimirAction_apply] at hc
  rw [mem_KWeightSpace_iff] at hv
  rw [hv, lie_smul, hv] at hc
  have hcomp :
      (4 : ℕ) • ⁅F, ⁅E, v⁆⁆ = -((n : ℂ) • (n : ℂ) • v + 2 • (n : ℂ) • v) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using hc
  calc
    (4 : ℂ) • ⁅F, ⁅E, v⁆⁆ = (4 : ℕ) • ⁅F, ⁅E, v⁆⁆ :=
      Nat.cast_smul_eq_nsmul ℂ 4 _
    _ =
        -((n : ℂ) • (n : ℂ) • v + 2 • (n : ℂ) • v) := hcomp
    _ = -((n : ℂ) * ((n : ℂ) + 2)) • v := by module

/-- On K-weight `n`, the equation `C = 0` gives the denominator-free
composition formula for first lowering and then raising. -/
theorem rho_E_F_formula {n : ℤ} {v : M}
    (hrho : HasRhoInfinitesimalCharacter M) (hv : v ∈ KWeightSpace M n) :
    (4 : ℂ) • ⁅E, ⁅F, v⁆⁆ = -((n : ℂ) * ((n : ℂ) - 2)) • v := by
  have hc : casimirAction M v = 0 := by rw [hrho]; rfl
  rw [casimirAction_alternative_apply] at hc
  rw [mem_KWeightSpace_iff] at hv
  rw [hv, lie_smul, hv] at hc
  have hcomp :
      (4 : ℕ) • ⁅E, ⁅F, v⁆⁆ = -((n : ℂ) • (n : ℂ) • v - 2 • (n : ℂ) • v) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using hc
  calc
    (4 : ℂ) • ⁅E, ⁅F, v⁆⁆ = (4 : ℕ) • ⁅E, ⁅F, v⁆⁆ :=
      Nat.cast_smul_eq_nsmul ℂ 4 _
    _ =
        -((n : ℂ) • (n : ℂ) • v - 2 • (n : ℂ) • v) := hcomp
    _ = -((n : ℂ) * ((n : ℂ) - 2)) • v := by module

end LieTheory.SL2RHarishChandra
