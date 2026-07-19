/-
Copyright (c) 2026 LieTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LieTheory contributors
-/
import LieTheory.SL2RHarishChandra.Models

/-! # K-type properties of the four explicit `SL₂(ℝ)` models -/

namespace LieTheory.SL2RHarishChandra

noncomputable section

variable {ι : Type*}

/-- The diagonal endomorphism of a Finsupp space with prescribed eigenvalues. -/
def diagonalEnd (w : ι → ℂ) : Module.End ℂ (ι →₀ ℂ) :=
  finsuppEndOfBasis fun i => Finsupp.single i (w i)

theorem diagonalEnd_apply_apply (w : ι → ℂ) (v : ι →₀ ℂ) (i : ι) :
    diagonalEnd w v i = w i * v i := by
  classical
  simp [diagonalEnd, finsuppEndOfBasis, Module.Basis.constr_apply,
    Finsupp.sum_apply, Finsupp.single_apply]
  by_cases h : v i = 0 <;> simp [h] <;> ring

/-- A Finsupp module whose standard basis has integral diagonal `H`-weights
is algebraically K-finite. -/
theorem isKFinite_diagonal (weight : ι → ℤ)
    [LieRingModule sl2Compact (ι →₀ ℂ)] [LieModule ℂ sl2Compact (ι →₀ ℂ)]
    (hH : LieModule.toEnd ℂ sl2Compact (ι →₀ ℂ) H =
      diagonalEnd (fun i => (weight i : ℂ))) :
    IsKFinite (ι →₀ ℂ) := by
  apply top_unique
  rw [← Finsupp.basisSingleOne.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  apply Submodule.mem_iSup_of_mem (weight i)
  rw [mem_KWeightSpace_iff]
  change (LieModule.toEnd ℂ sl2Compact (ι →₀ ℂ) H) (Finsupp.single i 1) = _
  rw [hH]
  ext j
  classical
  by_cases hji : j = i <;> simp [diagonalEnd_apply_apply, Finsupp.single_apply, hji]

private theorem coordinate_eq_zero_of_weight_ne
    (weight : ι → ℤ)
    [LieRingModule sl2Compact (ι →₀ ℂ)] [LieModule ℂ sl2Compact (ι →₀ ℂ)]
    (hH : LieModule.toEnd ℂ sl2Compact (ι →₀ ℂ) H =
      diagonalEnd (fun i => (weight i : ℂ)))
    {n : ℤ} {v : ι →₀ ℂ} (hv : v ∈ KWeightSpace (ι →₀ ℂ) n)
    (i : ι) (hne : weight i ≠ n) : v i = 0 := by
  rw [mem_KWeightSpace_iff] at hv
  change (LieModule.toEnd ℂ sl2Compact (ι →₀ ℂ) H) v = (n : ℂ) • v at hv
  rw [hH] at hv
  have hi := DFunLike.congr_fun hv i
  rw [diagonalEnd_apply_apply] at hi
  simp only [Finsupp.smul_apply] at hi
  have hc : (weight i : ℂ) ≠ (n : ℂ) := by exact_mod_cast hne
  have hz : ((weight i : ℂ) - (n : ℂ)) * v i = 0 := by
    linear_combination hi
  rcases mul_eq_zero.mp hz with hcoeff | hv
  · exact (sub_ne_zero.mpr hc hcoeff).elim
  · exact hv

/-- If the integral diagonal weights are distinct, every K-type has dimension
at most one, hence is finite-dimensional. -/
theorem isAdmissible_diagonal_of_injective [Inhabited ι] (weight : ι → ℤ)
    (hinj : Function.Injective weight)
    [LieRingModule sl2Compact (ι →₀ ℂ)] [LieModule ℂ sl2Compact (ι →₀ ℂ)]
    (hH : LieModule.toEnd ℂ sl2Compact (ι →₀ ℂ) H =
      diagonalEnd (fun i => (weight i : ℂ))) :
    IsAdmissible (ι →₀ ℂ) := by
  intro n
  classical
  by_cases hex : ∃ j, weight j = n
  · let j := Classical.choose hex
    have hj : weight j = n := Classical.choose_spec hex
    let ev : KWeightSpace (ι →₀ ℂ) n →ₗ[ℂ] ℂ :=
      (Finsupp.lapply j).domRestrict (KWeightSpace (ι →₀ ℂ) n)
    exact Module.Finite.of_injective ev (by
      intro x y hxy
      apply Subtype.ext
      apply Finsupp.ext
      intro i
      by_cases hij : i = j
      · subst i
        exact hxy
      · have hwi : weight i ≠ n := by
          intro hi
          apply hij
          exact hinj (hi.trans hj.symm)
        rw [coordinate_eq_zero_of_weight_ne weight hH x.2 i hwi,
          coordinate_eq_zero_of_weight_ne weight hH y.2 i hwi])
  · let ev : KWeightSpace (ι →₀ ℂ) n →ₗ[ℂ] ℂ :=
      (Finsupp.lapply (default : ι)).domRestrict (KWeightSpace (ι →₀ ℂ) n)
    exact Module.Finite.of_injective ev (by
      intro x y _
      apply Subtype.ext
      apply Finsupp.ext
      intro i
      have hwi : weight i ≠ n := fun hi => hex ⟨i, hi⟩
      rw [coordinate_eq_zero_of_weight_ne weight hH x.2 i hwi,
        coordinate_eq_zero_of_weight_ne weight hH y.2 i hwi])

theorem finrank_KWeightSpace_diagonal_le_one [Inhabited ι] (weight : ι → ℤ)
    (hinj : Function.Injective weight)
    [LieRingModule sl2Compact (ι →₀ ℂ)] [LieModule ℂ sl2Compact (ι →₀ ℂ)]
    (hH : LieModule.toEnd ℂ sl2Compact (ι →₀ ℂ) H =
      diagonalEnd (fun i => (weight i : ℂ))) (n : ℤ) :
    Module.finrank ℂ (KWeightSpace (ι →₀ ℂ) n) ≤ 1 := by
  classical
  by_cases hex : ∃ j, weight j = n
  · let j := Classical.choose hex
    have hj : weight j = n := Classical.choose_spec hex
    let ev : KWeightSpace (ι →₀ ℂ) n →ₗ[ℂ] ℂ :=
      (Finsupp.lapply j).domRestrict (KWeightSpace (ι →₀ ℂ) n)
    have hev : Function.Injective ev := by
      intro x y hxy
      apply Subtype.ext
      apply Finsupp.ext
      intro i
      by_cases hij : i = j
      · subst i
        exact hxy
      · have hwi : weight i ≠ n := by
          intro hi
          exact hij (hinj (hi.trans hj.symm))
        rw [coordinate_eq_zero_of_weight_ne weight hH x.2 i hwi,
          coordinate_eq_zero_of_weight_ne weight hH y.2 i hwi]
    simpa using LinearMap.finrank_le_finrank_of_injective hev
  · let ev : KWeightSpace (ι →₀ ℂ) n →ₗ[ℂ] ℂ :=
      (Finsupp.lapply (default : ι)).domRestrict (KWeightSpace (ι →₀ ℂ) n)
    have hev : Function.Injective ev := by
      intro x y _
      apply Subtype.ext
      apply Finsupp.ext
      intro i
      have hwi : weight i ≠ n := fun hi => hex ⟨i, hi⟩
      rw [coordinate_eq_zero_of_weight_ne weight hH x.2 i hwi,
        coordinate_eq_zero_of_weight_ne weight hH y.2 i hwi]
    simpa using LinearMap.finrank_le_finrank_of_injective hev

/-- The support of a diagonal Finsupp model is exactly the range of its
integral basis-weight function. -/
theorem mem_KSupport_diagonal_iff (weight : ι → ℤ)
    [LieRingModule sl2Compact (ι →₀ ℂ)] [LieModule ℂ sl2Compact (ι →₀ ℂ)]
    (hH : LieModule.toEnd ℂ sl2Compact (ι →₀ ℂ) H =
      diagonalEnd (fun i => (weight i : ℂ))) (n : ℤ) :
    n ∈ KSupport (ι →₀ ℂ) ↔ ∃ i, weight i = n := by
  rw [mem_KSupport_iff_exists_weight_vector]
  constructor
  · rintro ⟨v, hv⟩
    have hne : (v.1 : ι →₀ ℂ) ≠ 0 := by simpa using hv
    rcases Finsupp.ne_iff.mp hne with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    by_contra hwi
    exact hi (coordinate_eq_zero_of_weight_ne weight hH v.2 i hwi)
  · rintro ⟨i, rfl⟩
    refine ⟨⟨Finsupp.single i 1, ?_⟩, ?_⟩
    · rw [mem_KWeightSpace_iff]
      change (LieModule.toEnd ℂ sl2Compact (ι →₀ ℂ) H) (Finsupp.single i 1) = _
      rw [hH]
      ext j
      classical
      by_cases hji : j = i <;> simp [diagonalEnd_apply_apply, hji]
    · intro hzero
      apply Finsupp.single_ne_zero.mpr (one_ne_zero : (1 : ℂ) ≠ 0)
      exact congrArg Subtype.val hzero

def positiveWeight (j : ℕ) : ℤ := 2 + 2 * (j : ℤ)

def negativeWeight (j : NegativeIndex) : ℤ := -2 - 2 * (j.down : ℤ)

def oddWeight (j : ℤ) : ℤ := 2 * j + 1

theorem holomorphic_H_diagonal :
    LieModule.toEnd ℂ sl2Compact HolomorphicDiscreteHC H =
      diagonalEnd (fun j => (positiveWeight j : ℂ)) := by
  rw [holomorphic_toEnd_H]
  apply Finsupp.basisSingleOne.ext
  intro j
  simp [positiveH, diagonalEnd, positiveWeight]

theorem antiholomorphic_H_diagonal :
    LieModule.toEnd ℂ sl2Compact AntiholomorphicDiscreteHC H =
      diagonalEnd (fun j => (negativeWeight j : ℂ)) := by
  rw [antiholomorphic_toEnd_H]
  apply Finsupp.basisSingleOne.ext
  intro j
  simp [negativeH, diagonalEnd, negativeWeight]

theorem oddPrincipal_H_diagonal :
    LieModule.toEnd ℂ sl2Compact OddPrincipalHC H =
      diagonalEnd (fun j => (oddWeight j : ℂ)) := by
  rw [oddPrincipal_toEnd_H]
  apply Finsupp.basisSingleOne.ext
  intro j
  simp [oddH, diagonalEnd, oddWeight]

theorem positiveWeight_injective : Function.Injective positiveWeight := by
  intro i j h
  simp [positiveWeight] at h
  omega

theorem negativeWeight_injective : Function.Injective negativeWeight := by
  rintro ⟨i⟩ ⟨j⟩ h
  simp [negativeWeight] at h
  congr

theorem oddWeight_injective : Function.Injective oddWeight := by
  intro i j h
  simp [oddWeight] at h
  omega

theorem holomorphic_isKFinite : IsKFinite HolomorphicDiscreteHC :=
  isKFinite_diagonal positiveWeight holomorphic_H_diagonal

theorem holomorphic_isAdmissible : IsAdmissible HolomorphicDiscreteHC :=
  isAdmissible_diagonal_of_injective positiveWeight positiveWeight_injective
    holomorphic_H_diagonal

theorem holomorphic_isHarishChandraModule :
    IsHarishChandraModule HolomorphicDiscreteHC :=
  ⟨holomorphic_isKFinite, holomorphic_isAdmissible⟩

theorem antiholomorphic_isKFinite : IsKFinite AntiholomorphicDiscreteHC :=
  isKFinite_diagonal negativeWeight antiholomorphic_H_diagonal

theorem antiholomorphic_isAdmissible : IsAdmissible AntiholomorphicDiscreteHC :=
  isAdmissible_diagonal_of_injective negativeWeight negativeWeight_injective
    antiholomorphic_H_diagonal

theorem antiholomorphic_isHarishChandraModule :
    IsHarishChandraModule AntiholomorphicDiscreteHC :=
  ⟨antiholomorphic_isKFinite, antiholomorphic_isAdmissible⟩

theorem oddPrincipal_isKFinite : IsKFinite OddPrincipalHC :=
  isKFinite_diagonal oddWeight oddPrincipal_H_diagonal

theorem oddPrincipal_isAdmissible : IsAdmissible OddPrincipalHC :=
  isAdmissible_diagonal_of_injective oddWeight oddWeight_injective oddPrincipal_H_diagonal

theorem oddPrincipal_isHarishChandraModule : IsHarishChandraModule OddPrincipalHC :=
  ⟨oddPrincipal_isKFinite, oddPrincipal_isAdmissible⟩

theorem trivial_isKFinite : IsKFinite TrivialHC := by
  apply top_unique
  apply le_iSup_of_le (0 : ℤ)
  rw [KWeightSpace, trivial_toEnd]
  simp

theorem trivial_isAdmissible : IsAdmissible TrivialHC := by
  intro n
  infer_instance

theorem trivial_isHarishChandraModule : IsHarishChandraModule TrivialHC :=
  ⟨trivial_isKFinite, trivial_isAdmissible⟩

theorem holomorphic_support (n : ℤ) :
    n ∈ KSupport HolomorphicDiscreteHC ↔ ∃ j : ℕ, n = 2 + 2 * (j : ℤ) := by
  rw [mem_KSupport_diagonal_iff positiveWeight holomorphic_H_diagonal]
  simp only [positiveWeight]
  constructor <;> rintro ⟨j, rfl⟩ <;> exact ⟨j, rfl⟩

theorem antiholomorphic_support (n : ℤ) :
    n ∈ KSupport AntiholomorphicDiscreteHC ↔ ∃ j : ℕ, n = -2 - 2 * (j : ℤ) := by
  rw [mem_KSupport_diagonal_iff negativeWeight antiholomorphic_H_diagonal]
  constructor
  · rintro ⟨⟨j⟩, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨ULift.up j, rfl⟩

theorem oddPrincipal_support (n : ℤ) :
    n ∈ KSupport OddPrincipalHC ↔ n % 2 = 1 := by
  rw [mem_KSupport_diagonal_iff oddWeight oddPrincipal_H_diagonal]
  constructor
  · rintro ⟨j, rfl⟩
    simp [oddWeight, Int.add_emod, Int.mul_emod]
  · intro hn
    refine ⟨(n - 1) / 2, ?_⟩
    dsimp [oddWeight]
    omega

theorem trivial_support (n : ℤ) : n ∈ KSupport TrivialHC ↔ n = 0 := by
  rw [KSupport, Set.mem_setOf_eq, KWeightSpace, trivial_toEnd]
  constructor
  · intro h
    by_contra hn
    apply h
    ext v
    simp only [Module.End.mem_eigenspace_iff, LinearMap.zero_apply, zero_smul,
      Submodule.mem_bot]
    constructor
    · intro hv
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      exact (smul_eq_zero.mp hv.symm).resolve_left hnC
    · rintro rfl
      simp
  · rintro rfl
    simp

end

end LieTheory.SL2RHarishChandra
