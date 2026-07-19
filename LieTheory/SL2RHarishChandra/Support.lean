/-
Copyright (c) 2026 LieTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LieTheory contributors
-/
import LieTheory.SL2RHarishChandra.HarishChandraModule

/-!
# Weight transitions and support barriers for `SL₂(ℝ)`

This file packages the fixed operators `E` and `F` as linear maps between the
integer K-types of an algebraic `SL₂(ℝ)` module.  The Casimir relations show
that these maps are injective whenever the corresponding scalar is nonzero.
-/

namespace LieTheory.SL2RHarishChandra

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
variable [LieRingModule sl2Compact M] [LieModule ℂ sl2Compact M]

/-- Raising from weight `n` to weight `n + 2`. -/
def raisingMap (n : ℤ) : KWeightSpace M n →ₗ[ℂ] KWeightSpace M (n + 2) where
  toFun v := ⟨⁅E, v.1⁆, E_mem_KWeightSpace M v.2⟩
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp

/-- Lowering from weight `n` to weight `n - 2`. -/
def loweringMap (n : ℤ) : KWeightSpace M n →ₗ[ℂ] KWeightSpace M (n - 2) where
  toFun v := ⟨⁅F, v.1⁆, F_mem_KWeightSpace M v.2⟩
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp

/-- The lowering map whose target is written definitionally as weight `n`. -/
def loweringFromAbove (n : ℤ) : KWeightSpace M (n + 2) →ₗ[ℂ] KWeightSpace M n where
  toFun v := ⟨⁅F, v.1⁆, by simpa using F_mem_KWeightSpace M v.2⟩
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp

/-- The raising map whose target is written definitionally as weight `n`. -/
def raisingFromBelow (n : ℤ) : KWeightSpace M (n - 2) →ₗ[ℂ] KWeightSpace M n where
  toFun v := ⟨⁅E, v.1⁆, by simpa using E_mem_KWeightSpace M v.2⟩
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp

@[simp] theorem raisingMap_coe (n : ℤ) (v : KWeightSpace M n) :
    (raisingMap M n v : M) = ⁅E, (v : M)⁆ := rfl

@[simp] theorem loweringMap_coe (n : ℤ) (v : KWeightSpace M n) :
    (loweringMap M n v : M) = ⁅F, (v : M)⁆ := rfl

theorem lowering_raising_formula (hrho : HasRhoInfinitesimalCharacter M)
    (n : ℤ) (v : KWeightSpace M n) :
    (4 : ℂ) • loweringFromAbove M n (raisingMap M n v) =
      -((n : ℂ) * ((n : ℂ) + 2)) • v := by
  apply Subtype.ext
  exact rho_F_E_formula M hrho v.2

theorem raising_lowering_formula (hrho : HasRhoInfinitesimalCharacter M)
    (n : ℤ) (v : KWeightSpace M n) :
    (4 : ℂ) • raisingFromBelow M n (loweringMap M n v) =
      -((n : ℂ) * ((n : ℂ) - 2)) • v := by
  apply Subtype.ext
  exact rho_E_F_formula M hrho v.2

theorem raising_lowering_above_formula (hrho : HasRhoInfinitesimalCharacter M)
    (n : ℤ) (v : KWeightSpace M (n + 2)) :
    (4 : ℂ) • raisingMap M n (loweringFromAbove M n v) =
      -((n : ℂ) * ((n : ℂ) + 2)) • v := by
  apply Subtype.ext
  have h := rho_E_F_formula M hrho v.2
  change (4 : ℂ) • ⁅E, ⁅F, (v : M)⁆⁆ =
    -((n : ℂ) * ((n : ℂ) + 2)) • (v : M)
  have hs : ((n + 2 : ℤ) : ℂ) * (((n + 2 : ℤ) : ℂ) - 2) =
      (n : ℂ) * ((n : ℂ) + 2) := by
    push_cast
    ring
  rw [hs] at h
  exact h

theorem raisingMap_injective_of_coefficient_ne_zero
    (hrho : HasRhoInfinitesimalCharacter M) (n : ℤ)
    (hn : (n : ℂ) * ((n : ℂ) + 2) ≠ 0) :
    Function.Injective (raisingMap M n) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hformula := lowering_raising_formula M hrho n v
  rw [hv, map_zero, smul_zero] at hformula
  have hz : (-((n : ℂ) * ((n : ℂ) + 2))) • v = 0 := by simpa using hformula.symm
  rcases smul_eq_zero.mp hz with hcoeff | hv
  · exact (neg_ne_zero.mpr hn hcoeff).elim
  · exact hv

theorem loweringMap_injective_of_coefficient_ne_zero
    (hrho : HasRhoInfinitesimalCharacter M) (n : ℤ)
    (hn : (n : ℂ) * ((n : ℂ) - 2) ≠ 0) :
    Function.Injective (loweringMap M n) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hformula := raising_lowering_formula M hrho n v
  rw [hv, map_zero, smul_zero] at hformula
  have hz : (-((n : ℂ) * ((n : ℂ) - 2))) • v = 0 := by simpa using hformula.symm
  rcases smul_eq_zero.mp hz with hcoeff | hv
  · exact (neg_ne_zero.mpr hn hcoeff).elim
  · exact hv

theorem raising_coefficient_ne_zero (n : ℤ) (hzero : n ≠ 0) (hnegTwo : n ≠ -2) :
    (n : ℂ) * ((n : ℂ) + 2) ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast hzero
  · intro h
    apply hnegTwo
    have hn : (n : ℂ) = -2 := by linear_combination h
    exact_mod_cast hn

theorem lowering_coefficient_ne_zero (n : ℤ) (hzero : n ≠ 0) (htwo : n ≠ 2) :
    (n : ℂ) * ((n : ℂ) - 2) ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast hzero
  · intro h
    apply htwo
    have hn : (n : ℂ) = 2 := by linear_combination h
    exact_mod_cast hn

theorem raisingMap_surjective_of_coefficient_ne_zero
    (hrho : HasRhoInfinitesimalCharacter M) (n : ℤ)
    (hn : (n : ℂ) * ((n : ℂ) + 2) ≠ 0) :
    Function.Surjective (raisingMap M n) := by
  intro v
  let c : ℂ := -((n : ℂ) * ((n : ℂ) + 2))
  let s : ℂ := c⁻¹ * 4
  refine ⟨s • loweringFromAbove M n v, ?_⟩
  rw [map_smul]
  calc
    s • raisingMap M n (loweringFromAbove M n v) =
        c⁻¹ • ((4 : ℂ) • raisingMap M n (loweringFromAbove M n v)) := by
      dsimp [s]
      module
    _ = c⁻¹ • (c • v) := by
      rw [raising_lowering_above_formula M hrho]
    _ = v := by
      rw [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hn), one_smul]

/-- Away from the two even barriers `n = -2` and `n = 0`, raising gives a
linear equivalence between the adjacent K-types of weights `n` and `n + 2`. -/
noncomputable def raisingEquivOfCoefficientNeZero
    (hrho : HasRhoInfinitesimalCharacter M) (n : ℤ)
    (hn : (n : ℂ) * ((n : ℂ) + 2) ≠ 0) :
    KWeightSpace M n ≃ₗ[ℂ] KWeightSpace M (n + 2) :=
  LinearEquiv.ofBijective (raisingMap M n)
    ⟨raisingMap_injective_of_coefficient_ne_zero M hrho n hn,
      raisingMap_surjective_of_coefficient_ne_zero M hrho n hn⟩

/-- The usable barrier form of `raisingEquivOfCoefficientNeZero`. -/
noncomputable def raisingEquivAwayFromBarriers
    (hrho : HasRhoInfinitesimalCharacter M) (n : ℤ)
    (hzero : n ≠ 0) (hnegTwo : n ≠ -2) :
    KWeightSpace M n ≃ₗ[ℂ] KWeightSpace M (n + 2) :=
  raisingEquivOfCoefficientNeZero M hrho n
    (raising_coefficient_ne_zero n hzero hnegTwo)

theorem mem_KSupport_iff_exists_weight_vector (n : ℤ) :
    n ∈ KSupport M ↔ ∃ v : KWeightSpace M n, v ≠ 0 := by
  rw [KSupport, Set.mem_setOf_eq, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨v, hv, hv0⟩
    exact ⟨⟨v, hv⟩, by simpa using hv0⟩
  · rintro ⟨v, hv⟩
    exact ⟨v.1, v.2, by simpa using hv⟩

/-- Away from the barriers, adjacent weights occur simultaneously. -/
theorem mem_KSupport_add_two_iff
    (hrho : HasRhoInfinitesimalCharacter M) (n : ℤ)
    (hzero : n ≠ 0) (hnegTwo : n ≠ -2) :
    n + 2 ∈ KSupport M ↔ n ∈ KSupport M := by
  let e := raisingEquivAwayFromBarriers M hrho n hzero hnegTwo
  rw [mem_KSupport_iff_exists_weight_vector, mem_KSupport_iff_exists_weight_vector]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨e.symm v, ?_⟩
    exact e.symm.map_ne_zero_iff.mpr hv
  · rintro ⟨v, hv⟩
    refine ⟨e v, ?_⟩
    exact e.map_ne_zero_iff.mpr hv

theorem odd_mem_KSupport_add_two_iff
    (hrho : HasRhoInfinitesimalCharacter M) (n : ℤ) (hnodd : n % 2 = 1) :
    n + 2 ∈ KSupport M ↔ n ∈ KSupport M := by
  apply mem_KSupport_add_two_iff M hrho n
  · omega
  · omega

theorem odd_support_propagates_up
    (hrho : HasRhoInfinitesimalCharacter M) (n : ℤ) (hnodd : n % 2 = 1)
    (hn : n ∈ KSupport M) :
    ∀ k : ℕ, n + 2 * (k : ℤ) ∈ KSupport M := by
  intro k
  induction k with
  | zero => simpa using hn
  | succ k ih =>
      have hodd : (n + 2 * (k : ℤ)) % 2 = 1 := by
        simpa [Int.add_emod, Int.mul_emod] using hnodd
      have hnext := (odd_mem_KSupport_add_two_iff M hrho
        (n + 2 * (k : ℤ)) hodd).mpr ih
      convert hnext using 1 <;> push_cast <;> ring

theorem odd_support_propagates_down
    (hrho : HasRhoInfinitesimalCharacter M) (n : ℤ) (hnodd : n % 2 = 1)
    (hn : n ∈ KSupport M) :
    ∀ k : ℕ, n - 2 * (k : ℤ) ∈ KSupport M := by
  intro k
  induction k with
  | zero => simpa using hn
  | succ k ih =>
      have hodd : (n - 2 * ((k + 1 : ℕ) : ℤ)) % 2 = 1 := by
        omega
      have hedge := odd_mem_KSupport_add_two_iff M hrho
        (n - 2 * ((k + 1 : ℕ) : ℤ)) hodd
      apply hedge.mp
      convert ih using 1 <;> push_cast <;> ring

end LieTheory.SL2RHarishChandra
