/-
Copyright (c) 2026 SL2RepresentationTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SL2RepresentationTheory contributors
-/
import SL2RepresentationTheory.SL2RHarishChandra.ModelProperties

/-! # Irreducibility of the four explicit `SL₂(ℝ)` models -/

namespace SL2RepresentationTheory.SL2RHarishChandra

noncomputable section

variable {ι : Type*}

/-- An invariant subspace of a diagonal Finsupp model contains every nonzero
standard-basis component of each of its vectors.  This is the finite-support
spectral-projection argument, proved without assuming a general weight theory. -/
theorem single_component_mem_lieSubmodule
    [DecidableEq ι] (weight : ι → ℤ) (hinj : Function.Injective weight)
    [LieRingModule sl2Compact (ι →₀ ℂ)] [LieModule ℂ sl2Compact (ι →₀ ℂ)]
    (hH : LieModule.toEnd ℂ sl2Compact (ι →₀ ℂ) H =
      diagonalEnd (fun i => (weight i : ℂ)))
    (N : LieSubmodule ℂ sl2Compact (ι →₀ ℂ))
    {v : ι →₀ ℂ} (hvN : v ∈ N) (i : ι) (hvi : v i ≠ 0) :
    Finsupp.single i (v i) ∈ N := by
  generalize hm : v.support.card = m
  induction m using Nat.strong_induction_on generalizing v with
  | h m ih =>
      by_cases herase : v.support.erase i = ∅
      · have hsupp : v.support ⊆ {i} := by
          intro a ha
          by_cases hai : a = i
          · simpa [hai]
          have : a ∈ v.support.erase i := Finset.mem_erase.mpr ⟨hai, ha⟩
          simp [herase] at this
        have hv_single : v = Finsupp.single i (v i) := by
          apply Finsupp.ext
          intro a
          by_cases hai : a = i
          · subst a
            simp
          · have ha0 : v a = 0 := by
              by_contra ha
              apply hai
              simpa using hsupp (Finsupp.mem_support_iff.mpr ha)
            simp [hai, ha0]
        rwa [← hv_single]
      · rcases Finset.nonempty_iff_ne_empty.mpr herase with ⟨k, hk⟩
        have hki : k ≠ i := (Finset.mem_erase.mp hk).1
        have hkv : k ∈ v.support := (Finset.mem_erase.mp hk).2
        let c : ℂ := (weight k : ℂ)
        let w : ι →₀ ℂ := diagonalEnd (fun a => (weight a : ℂ)) v - c • v
        have hw_apply (a : ι) :
            w a = ((weight a : ℂ) - (weight k : ℂ)) * v a := by
          simp [w, c, diagonalEnd_apply_apply, sub_mul]
        have hwN : w ∈ N := by
          apply sub_mem
          · rw [← hH]
            exact N.lie_mem hvN
          · exact (N : Submodule ℂ (ι →₀ ℂ)).smul_mem c hvN
        have hwi : w i ≠ 0 := by
          rw [hw_apply]
          apply mul_ne_zero
          · apply sub_ne_zero.mpr
            have hwne : weight i ≠ weight k := by
              intro h
              exact hki (hinj h).symm
            exact_mod_cast hwne
          · exact hvi
        have hw_subset : w.support ⊆ v.support.erase k := by
          intro a ha
          rw [Finset.mem_erase]
          constructor
          · intro hak
            subst a
            exact (Finsupp.mem_support_iff.mp ha) (by simp [hw_apply])
          · apply Finsupp.mem_support_iff.mpr
            intro hva
            exact (Finsupp.mem_support_iff.mp ha) (by simp [hw_apply, hva])
        have hcard : w.support.card < v.support.card :=
          lt_of_le_of_lt (Finset.card_le_card hw_subset)
            (Finset.card_erase_lt_of_mem hkv)
        have hw_single : Finsupp.single i (w i) ∈ N :=
          ih w.support.card (hm ▸ hcard) hwN hwi rfl
        have hcik : ((weight i : ℂ) - (weight k : ℂ)) ≠ 0 := by
          apply sub_ne_zero.mpr
          have hwne : weight i ≠ weight k := by
            intro h
            exact hki (hinj h).symm
          exact_mod_cast hwne
        have hscale := (N : Submodule ℂ (ι →₀ ℂ)).smul_mem
          (((weight i : ℂ) - (weight k : ℂ))⁻¹) hw_single
        have heq : (((weight i : ℂ) - (weight k : ℂ))⁻¹) •
            Finsupp.single i (w i) = Finsupp.single i (v i) := by
          ext a
          classical
          by_cases hai : a = i
          · subst a
            simp [hw_apply, hcik]
          · simp [hai]
        rwa [← heq]

private theorem basis_mem_of_single_mem
    [DecidableEq ι]
    [LieRingModule sl2Compact (ι →₀ ℂ)] [LieModule ℂ sl2Compact (ι →₀ ℂ)]
    (N : LieSubmodule ℂ sl2Compact (ι →₀ ℂ))
    (i : ι) (c : ℂ) (hc : c ≠ 0) (hmem : Finsupp.single i c ∈ N) :
    Finsupp.single i 1 ∈ N := by
  have h := (N : Submodule ℂ (ι →₀ ℂ)).smul_mem c⁻¹ hmem
  simpa [Finsupp.smul_single, hc] using h

private theorem exists_basis_mem_of_ne_bot
    [DecidableEq ι] (weight : ι → ℤ) (hinj : Function.Injective weight)
    [LieRingModule sl2Compact (ι →₀ ℂ)] [LieModule ℂ sl2Compact (ι →₀ ℂ)]
    (hH : LieModule.toEnd ℂ sl2Compact (ι →₀ ℂ) H =
      diagonalEnd (fun i => (weight i : ℂ)))
    (N : LieSubmodule ℂ sl2Compact (ι →₀ ℂ)) (hN : N ≠ ⊥) :
    ∃ i, Finsupp.single i 1 ∈ N := by
  have hNsub : (N : Submodule ℂ (ι →₀ ℂ)) ≠ ⊥ := by
    intro hbot
    apply hN
    ext v
    change v ∈ (N : Submodule ℂ (ι →₀ ℂ)) ↔ v ∈ (⊥ : Submodule ℂ (ι →₀ ℂ))
    rw [hbot]
  rcases (Submodule.ne_bot_iff (N : Submodule ℂ (ι →₀ ℂ))).mp hNsub with
    ⟨v, hvN, hv0⟩
  rcases Finsupp.ne_iff.mp hv0 with ⟨i, hi⟩
  refine ⟨i, basis_mem_of_single_mem N i (v i) hi ?_⟩
  exact single_component_mem_lieSubmodule weight hinj hH N hvN i hi

private theorem holomorphic_lower_to_zero
    (N : LieSubmodule ℂ sl2Compact HolomorphicDiscreteHC) :
    ∀ j : ℕ, Finsupp.single j 1 ∈ N → Finsupp.single 0 1 ∈ N := by
  intro j
  induction j with
  | zero => exact id
  | succ j ih =>
      intro hj
      have hact : ⁅F, (Finsupp.single (j + 1) 1 : HolomorphicDiscreteHC)⁆ ∈ N :=
        N.lie_mem hj
      rw [holomorphic_F_single] at hact
      simp only [positiveFImage] at hact
      have hc : (-((j + 1 : ℕ) : ℂ)) * ((j + 2 : ℕ) : ℂ) ≠ 0 := by
        apply mul_ne_zero
        · exact neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero j)
        · exact_mod_cast Nat.succ_ne_zero (j + 1)
      exact ih (basis_mem_of_single_mem N j _ hc hact)

private theorem holomorphic_raise_from_zero
    (N : LieSubmodule ℂ sl2Compact HolomorphicDiscreteHC)
    (hzero : Finsupp.single 0 1 ∈ N) :
    ∀ j : ℕ, Finsupp.single j 1 ∈ N := by
  intro j
  induction j with
  | zero => exact hzero
  | succ j ih =>
      have hact : ⁅E, (Finsupp.single j 1 : HolomorphicDiscreteHC)⁆ ∈ N :=
        N.lie_mem ih
      simpa using hact

noncomputable instance holomorphic_isIrreducible :
    LieModule.IsIrreducible ℂ sl2Compact HolomorphicDiscreteHC := by
  apply LieModule.IsIrreducible.mk
  intro N hN
  rcases exists_basis_mem_of_ne_bot positiveWeight positiveWeight_injective
    holomorphic_H_diagonal N hN with ⟨j, hj⟩
  have hzero := holomorphic_lower_to_zero N j hj
  have hall := holomorphic_raise_from_zero N hzero
  apply top_unique
  change (⊤ : Submodule ℂ HolomorphicDiscreteHC) ≤
    (N : Submodule ℂ HolomorphicDiscreteHC)
  rw [← Finsupp.basisSingleOne.span_eq]
  exact Submodule.span_le.mpr (by
    rintro _ ⟨j, rfl⟩
    exact hall j)

private theorem antiholomorphic_lower_to_zero
    (N : LieSubmodule ℂ sl2Compact AntiholomorphicDiscreteHC) :
    ∀ j : ℕ, Finsupp.single (ULift.up j) 1 ∈ N →
      Finsupp.single (ULift.up 0) 1 ∈ N := by
  intro j
  induction j with
  | zero => exact id
  | succ j ih =>
      intro hj
      have hact : ⁅E, (Finsupp.single (ULift.up (j + 1)) 1 :
          AntiholomorphicDiscreteHC)⁆ ∈ N := N.lie_mem hj
      rw [antiholomorphic_E_single] at hact
      simp only [negativeEImage] at hact
      have hc : (-((j + 1 : ℕ) : ℂ)) * ((j + 2 : ℕ) : ℂ) ≠ 0 := by
        apply mul_ne_zero
        · exact neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero j)
        · exact_mod_cast Nat.succ_ne_zero (j + 1)
      exact ih (basis_mem_of_single_mem N (ULift.up j) _ hc hact)

private theorem antiholomorphic_raise_from_zero
    (N : LieSubmodule ℂ sl2Compact AntiholomorphicDiscreteHC)
    (hzero : Finsupp.single (ULift.up 0) 1 ∈ N) :
    ∀ j : ℕ, Finsupp.single (ULift.up j) 1 ∈ N := by
  intro j
  induction j with
  | zero => exact hzero
  | succ j ih =>
      have hact : ⁅F, (Finsupp.single (ULift.up j) 1 :
          AntiholomorphicDiscreteHC)⁆ ∈ N := N.lie_mem ih
      simpa using hact

noncomputable instance antiholomorphic_isIrreducible :
    LieModule.IsIrreducible ℂ sl2Compact AntiholomorphicDiscreteHC := by
  apply LieModule.IsIrreducible.mk
  intro N hN
  rcases exists_basis_mem_of_ne_bot negativeWeight negativeWeight_injective
    antiholomorphic_H_diagonal N hN with ⟨⟨j⟩, hj⟩
  have hzero := antiholomorphic_lower_to_zero N j hj
  have hall := antiholomorphic_raise_from_zero N hzero
  apply top_unique
  change (⊤ : Submodule ℂ AntiholomorphicDiscreteHC) ≤
    (N : Submodule ℂ AntiholomorphicDiscreteHC)
  rw [← Finsupp.basisSingleOne.span_eq]
  exact Submodule.span_le.mpr (by
    rintro _ ⟨⟨j⟩, rfl⟩
    exact hall j)

theorem oddFCoefficient_ne_zero (j : ℤ) :
    ((1 - 4 * (j : ℂ) ^ 2) / 4) ≠ 0 := by
  apply div_ne_zero
  · intro h
    have hz : (1 : ℤ) - 4 * j ^ 2 = 0 := by exact_mod_cast h
    have hm := congrArg (fun z : ℤ => z % 2) hz
    norm_num [Int.sub_emod, Int.mul_emod] at hm
  · norm_num

private theorem odd_raise_one (N : LieSubmodule ℂ sl2Compact OddPrincipalHC)
    (j : ℤ) (hj : Finsupp.single j 1 ∈ N) : Finsupp.single (j + 1) 1 ∈ N := by
  have hact : ⁅E, (Finsupp.single j 1 : OddPrincipalHC)⁆ ∈ N := N.lie_mem hj
  simpa using hact

private theorem odd_lower_one (N : LieSubmodule ℂ sl2Compact OddPrincipalHC)
    (j : ℤ) (hj : Finsupp.single j 1 ∈ N) : Finsupp.single (j - 1) 1 ∈ N := by
  have hact : ⁅F, (Finsupp.single j 1 : OddPrincipalHC)⁆ ∈ N := N.lie_mem hj
  rw [oddPrincipal_F_single] at hact
  exact basis_mem_of_single_mem N (j - 1) _ (oddFCoefficient_ne_zero j) hact

private theorem odd_raise_nat (N : LieSubmodule ℂ sl2Compact OddPrincipalHC)
    (j : ℤ) (hj : Finsupp.single j 1 ∈ N) :
    ∀ k : ℕ, Finsupp.single (j + (k : ℤ)) 1 ∈ N := by
  intro k
  induction k with
  | zero => simpa using hj
  | succ k ih =>
      convert odd_raise_one N (j + (k : ℤ)) ih using 1 <;> push_cast <;> ring

private theorem odd_lower_nat (N : LieSubmodule ℂ sl2Compact OddPrincipalHC)
    (j : ℤ) (hj : Finsupp.single j 1 ∈ N) :
    ∀ k : ℕ, Finsupp.single (j - (k : ℤ)) 1 ∈ N := by
  intro k
  induction k with
  | zero => simpa using hj
  | succ k ih =>
      convert odd_lower_one N (j - (k : ℤ)) ih using 1 <;> push_cast <;> ring

private theorem odd_all_basis_from_one
    (N : LieSubmodule ℂ sl2Compact OddPrincipalHC) (i : ℤ)
    (hi : Finsupp.single i 1 ∈ N) : ∀ j : ℤ, Finsupp.single j 1 ∈ N := by
  intro j
  by_cases hij : i ≤ j
  · have hk : (0 : ℤ) ≤ j - i := sub_nonneg.mpr hij
    have h := odd_raise_nat N i hi (j - i).toNat
    rw [Int.toNat_of_nonneg hk] at h
    convert h using 1 <;> ring
  · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
    have hk : (0 : ℤ) ≤ i - j := sub_nonneg.mpr hji
    have h := odd_lower_nat N i hi (i - j).toNat
    rw [Int.toNat_of_nonneg hk] at h
    convert h using 1 <;> ring

noncomputable instance oddPrincipal_isIrreducible :
    LieModule.IsIrreducible ℂ sl2Compact OddPrincipalHC := by
  apply LieModule.IsIrreducible.mk
  intro N hN
  rcases exists_basis_mem_of_ne_bot oddWeight oddWeight_injective
    oddPrincipal_H_diagonal N hN with ⟨i, hi⟩
  have hall := odd_all_basis_from_one N i hi
  apply top_unique
  change (⊤ : Submodule ℂ OddPrincipalHC) ≤ (N : Submodule ℂ OddPrincipalHC)
  rw [← Finsupp.basisSingleOne.span_eq]
  exact Submodule.span_le.mpr (by
    rintro _ ⟨j, rfl⟩
    exact hall j)

noncomputable instance trivial_isIrreducible :
    LieModule.IsIrreducible ℂ sl2Compact TrivialHC := by
  apply LieModule.IsIrreducible.mk
  intro N hN
  have hNsub : (N : Submodule ℂ TrivialHC) ≠ ⊥ := by
    intro hbot
    apply hN
    ext v
    change v ∈ (N : Submodule ℂ TrivialHC) ↔ v ∈ (⊥ : Submodule ℂ TrivialHC)
    rw [hbot]
  rcases (Submodule.ne_bot_iff (N : Submodule ℂ TrivialHC)).mp hNsub with
    ⟨v, hvN, hv0⟩
  apply top_unique
  intro x _
  have hmem := (N : Submodule ℂ TrivialHC).smul_mem (x / v) hvN
  have hx : (x / v) • v = x := by
    change (x / v) * v = x
    exact div_mul_cancel₀ x hv0
  rw [← hx]
  exact hmem

end

end SL2RepresentationTheory.SL2RHarishChandra
