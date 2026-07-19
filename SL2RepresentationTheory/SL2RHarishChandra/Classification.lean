/-
Copyright (c) 2026 SL2RepresentationTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SL2RepresentationTheory contributors
-/
import SL2RepresentationTheory.SL2RHarishChandra.Irreducibility

/-! # Classification at the rho infinitesimal character -/

namespace SL2RepresentationTheory.SL2RHarishChandra

noncomputable section

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
variable [LieRingModule sl2Compact M] [LieModule ℂ sl2Compact M]

private theorem support_nonempty [Nontrivial M] (hK : IsKFinite M) :
    ∃ n, n ∈ KSupport M := by
  by_contra h
  have hall : ∀ n : ℤ, KWeightSpace M n = ⊥ := by
    intro n
    by_contra hn
    exact h ⟨n, hn⟩
  have hiSup : (⨆ n : ℤ, KWeightSpace M n) = ⊥ := by simp [hall]
  rw [hK] at hiSup
  exact (bot_ne_top hiSup.symm)

private theorem even_descends_to_two (hrho : HasRhoInfinitesimalCharacter M) :
    ∀ k : ℕ, 2 + 2 * (k : ℤ) ∈ KSupport M → 2 ∈ KSupport M := by
  intro k
  induction k with
  | zero => simpa
  | succ k ih =>
      intro hs
      have hedge := mem_KSupport_add_two_iff M hrho (2 + 2 * (k : ℤ)) (by omega) (by omega)
      apply ih
      apply hedge.mp
      convert hs using 1 <;> push_cast <;> ring

private theorem even_ascends_to_neg_two (hrho : HasRhoInfinitesimalCharacter M) :
    ∀ k : ℕ, -2 - 2 * (k : ℤ) ∈ KSupport M → -2 ∈ KSupport M := by
  intro k
  induction k with
  | zero => simpa
  | succ k ih =>
      intro hs
      have hedge := mem_KSupport_add_two_iff M hrho
        (-2 - 2 * ((k + 1 : ℕ) : ℤ)) (by omega) (by omega)
      apply ih
      have := hedge.mpr hs
      convert this using 1 <;> push_cast <;> ring

private theorem odd_reaches_one (hrho : HasRhoInfinitesimalCharacter M)
    (n : ℤ) (hnodd : n % 2 = 1) (hn : n ∈ KSupport M) :
    1 ∈ KSupport M := by
  by_cases hle : n ≤ 1
  · let k : ℕ := ((1 - n) / 2).toNat
    have hk0 : 0 ≤ (1 - n) / 2 := by omega
    have heq : n + 2 * (k : ℤ) = 1 := by
      dsimp [k]
      rw [Int.toNat_of_nonneg hk0]
      omega
    rw [← heq]
    exact odd_support_propagates_up M hrho n hnodd hn k
  · let k : ℕ := ((n - 1) / 2).toNat
    have hk0 : 0 ≤ (n - 1) / 2 := by omega
    have heq : n - 2 * (k : ℤ) = 1 := by
      dsimp [k]
      rw [Int.toNat_of_nonneg hk0]
      omega
    rw [← heq]
    exact odd_support_propagates_down M hrho n hnodd hn k

private theorem even_reaches_barrier (hrho : HasRhoInfinitesimalCharacter M)
    (n : ℤ) (hneven : n % 2 = 0) (hn : n ∈ KSupport M) :
    0 ∈ KSupport M ∨ 2 ∈ KSupport M ∨ -2 ∈ KSupport M := by
  rcases lt_trichotomy n 0 with hnneg | rfl | hnpos
  · have hnle : n ≤ -2 := by omega
    let k : ℕ := ((-2 - n) / 2).toNat
    have hk0 : 0 ≤ (-2 - n) / 2 := by omega
    have heq : n = -2 - 2 * (k : ℤ) := by
      dsimp [k]
      rw [Int.toNat_of_nonneg hk0]
      omega
    right; right
    rw [heq] at hn
    exact even_ascends_to_neg_two M hrho k hn
  · exact Or.inl hn
  · have hnle : 2 ≤ n := by omega
    let k : ℕ := ((n - 2) / 2).toNat
    have hk0 : 0 ≤ (n - 2) / 2 := by omega
    have heq : n = 2 + 2 * (k : ℤ) := by
      dsimp [k]
      rw [Int.toNat_of_nonneg hk0]
      omega
    right; left
    rw [heq] at hn
    exact even_descends_to_two M hrho k hn

def IsTrivialSeed (v : M) : Prop :=
  v ≠ 0 ∧ v ∈ KWeightSpace M 0 ∧ ⁅E, v⁆ = 0 ∧ ⁅F, v⁆ = 0

def IsPositiveSeed (v : M) : Prop :=
  v ≠ 0 ∧ v ∈ KWeightSpace M 2 ∧ ⁅F, v⁆ = 0

def IsNegativeSeed (v : M) : Prop :=
  v ≠ 0 ∧ v ∈ KWeightSpace M (-2) ∧ ⁅E, v⁆ = 0

def IsOddSeed (v : M) : Prop := v ≠ 0 ∧ v ∈ KWeightSpace M 1

private theorem rho_EF_zero_at_weight_zero
    (hrho : HasRhoInfinitesimalCharacter M) {v : M}
    (hv : v ∈ KWeightSpace M 0) : ⁅E, ⁅F, v⁆⁆ = 0 := by
  have h := rho_E_F_formula M hrho hv
  norm_num at h
  exact h

private theorem rho_FE_zero_at_weight_zero
    (hrho : HasRhoInfinitesimalCharacter M) {v : M}
    (hv : v ∈ KWeightSpace M 0) : ⁅F, ⁅E, v⁆⁆ = 0 := by
  have h := rho_F_E_formula M hrho hv
  norm_num at h
  exact h

private theorem rho_EF_zero_at_weight_two
    (hrho : HasRhoInfinitesimalCharacter M) {v : M}
    (hv : v ∈ KWeightSpace M 2) : ⁅E, ⁅F, v⁆⁆ = 0 := by
  have h := rho_E_F_formula M hrho hv
  norm_num at h
  exact h

private theorem rho_FE_zero_at_weight_neg_two
    (hrho : HasRhoInfinitesimalCharacter M) {v : M}
    (hv : v ∈ KWeightSpace M (-2)) : ⁅F, ⁅E, v⁆⁆ = 0 := by
  have h := rho_F_E_formula M hrho hv
  norm_num at h
  exact h

private theorem seed_of_weight_zero (hrho : HasRhoInfinitesimalCharacter M)
    (h0 : 0 ∈ KSupport M) :
    (∃ v, IsTrivialSeed M v) ∨ (∃ v, IsPositiveSeed M v) ∨
      (∃ v, IsNegativeSeed M v) := by
  rcases (mem_KSupport_iff_exists_weight_vector M 0).mp h0 with ⟨v, hv⟩
  by_cases hEv : ⁅E, (v : M)⁆ = 0
  · by_cases hFv : ⁅F, (v : M)⁆ = 0
    · refine Or.inl ⟨v, ?_⟩
      change (v : M) ≠ 0 ∧ (v : M) ∈ KWeightSpace M 0 ∧
        ⁅E, (v : M)⁆ = 0 ∧ ⁅F, (v : M)⁆ = 0
      exact ⟨by simpa using hv, v.2, hEv, hFv⟩
    · refine Or.inr (Or.inr ⟨⁅F, (v : M)⁆, ?_⟩)
      change ⁅F, (v : M)⁆ ≠ 0 ∧ ⁅F, (v : M)⁆ ∈ KWeightSpace M (-2) ∧
        ⁅E, ⁅F, (v : M)⁆⁆ = 0
      have hweight : ⁅F, (v : M)⁆ ∈ KWeightSpace M (-2) := by
        simpa using F_mem_KWeightSpace M v.2
      have hzero : ⁅E, ⁅F, (v : M)⁆⁆ = 0 :=
        rho_EF_zero_at_weight_zero M hrho v.2
      exact ⟨hFv, hweight, hzero⟩
  · refine Or.inr (Or.inl ⟨⁅E, (v : M)⁆, ?_⟩)
    change ⁅E, (v : M)⁆ ≠ 0 ∧ ⁅E, (v : M)⁆ ∈ KWeightSpace M 2 ∧
      ⁅F, ⁅E, (v : M)⁆⁆ = 0
    have hweight : ⁅E, (v : M)⁆ ∈ KWeightSpace M 2 := by
      simpa using E_mem_KWeightSpace M v.2
    have hzero : ⁅F, ⁅E, (v : M)⁆⁆ = 0 :=
      rho_FE_zero_at_weight_zero M hrho v.2
    exact ⟨hEv, hweight, hzero⟩

private theorem seed_of_weight_two (hrho : HasRhoInfinitesimalCharacter M)
    (h2 : 2 ∈ KSupport M) :
    (∃ v, IsTrivialSeed M v) ∨ (∃ v, IsPositiveSeed M v) ∨
      (∃ v, IsNegativeSeed M v) := by
  rcases (mem_KSupport_iff_exists_weight_vector M 2).mp h2 with ⟨v, hv⟩
  by_cases hFv : ⁅F, (v : M)⁆ = 0
  · refine Or.inr (Or.inl ⟨v, ?_⟩)
    change (v : M) ≠ 0 ∧ (v : M) ∈ KWeightSpace M 2 ∧ ⁅F, (v : M)⁆ = 0
    exact ⟨by simpa using hv, v.2, hFv⟩
  · let w : M := ⁅F, (v : M)⁆
    have hw0 : w ∈ KWeightSpace M 0 := by simpa [w] using F_mem_KWeightSpace M v.2
    have hEw : ⁅E, w⁆ = 0 := by simpa [w] using rho_EF_zero_at_weight_two M hrho v.2
    by_cases hFw : ⁅F, w⁆ = 0
    · refine Or.inl ⟨w, ?_⟩
      change w ≠ 0 ∧ w ∈ KWeightSpace M 0 ∧ ⁅E, w⁆ = 0 ∧ ⁅F, w⁆ = 0
      exact ⟨hFv, hw0, hEw, hFw⟩
    · refine Or.inr (Or.inr ⟨⁅F, w⁆, ?_⟩)
      change ⁅F, w⁆ ≠ 0 ∧ ⁅F, w⁆ ∈ KWeightSpace M (-2) ∧ ⁅E, ⁅F, w⁆⁆ = 0
      have hweight : ⁅F, w⁆ ∈ KWeightSpace M (-2) := by
        simpa using F_mem_KWeightSpace M hw0
      have hzero : ⁅E, ⁅F, w⁆⁆ = 0 := rho_EF_zero_at_weight_zero M hrho hw0
      exact ⟨hFw, hweight, hzero⟩

private theorem seed_of_weight_neg_two (hrho : HasRhoInfinitesimalCharacter M)
    (hm2 : -2 ∈ KSupport M) :
    (∃ v, IsTrivialSeed M v) ∨ (∃ v, IsPositiveSeed M v) ∨
      (∃ v, IsNegativeSeed M v) := by
  rcases (mem_KSupport_iff_exists_weight_vector M (-2)).mp hm2 with ⟨v, hv⟩
  by_cases hEv : ⁅E, (v : M)⁆ = 0
  · refine Or.inr (Or.inr ⟨v, ?_⟩)
    change (v : M) ≠ 0 ∧ (v : M) ∈ KWeightSpace M (-2) ∧ ⁅E, (v : M)⁆ = 0
    exact ⟨by simpa using hv, v.2, hEv⟩
  · let w : M := ⁅E, (v : M)⁆
    have hw0 : w ∈ KWeightSpace M 0 := by simpa [w] using E_mem_KWeightSpace M v.2
    have hFw : ⁅F, w⁆ = 0 := by simpa [w] using rho_FE_zero_at_weight_neg_two M hrho v.2
    by_cases hEw : ⁅E, w⁆ = 0
    · refine Or.inl ⟨w, ?_⟩
      change w ≠ 0 ∧ w ∈ KWeightSpace M 0 ∧ ⁅E, w⁆ = 0 ∧ ⁅F, w⁆ = 0
      exact ⟨hEv, hw0, hEw, hFw⟩
    · refine Or.inr (Or.inl ⟨⁅E, w⁆, ?_⟩)
      change ⁅E, w⁆ ≠ 0 ∧ ⁅E, w⁆ ∈ KWeightSpace M 2 ∧ ⁅F, ⁅E, w⁆⁆ = 0
      have hweight : ⁅E, w⁆ ∈ KWeightSpace M 2 := by
        simpa using E_mem_KWeightSpace M hw0
      have hzero : ⁅F, ⁅E, w⁆⁆ = 0 := rho_FE_zero_at_weight_zero M hrho hw0
      exact ⟨hEw, hweight, hzero⟩

/-- The four possible algebraic seed vectors. Once a seed exists, the
Casimir recurrence determines the complete model map. -/
theorem exists_rho_seed [Nontrivial M] [LieModule.IsIrreducible ℂ sl2Compact M]
    (hK : IsKFinite M) (hrho : HasRhoInfinitesimalCharacter M) :
    (∃ v, IsTrivialSeed M v) ∨ (∃ v, IsPositiveSeed M v) ∨
      (∃ v, IsNegativeSeed M v) ∨ (∃ v, IsOddSeed M v) := by
  rcases support_nonempty M hK with ⟨n, hn⟩
  rcases irreducible_support_has_fixed_parity M hK with heven | hodd
  · rcases even_reaches_barrier M hrho n (heven n hn) hn with h0 | h2 | hm2
    · rcases seed_of_weight_zero M hrho h0 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · rcases seed_of_weight_two M hrho h2 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · rcases seed_of_weight_neg_two M hrho hm2 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
  · have h1 := odd_reaches_one M hrho n (hodd n hn) hn
    rcases (mem_KSupport_iff_exists_weight_vector M 1).mp h1 with ⟨v, hv⟩
    refine Or.inr (Or.inr (Or.inr ⟨v, ?_⟩))
    exact ⟨by simpa using hv, v.2⟩

end

end SL2RepresentationTheory.SL2RHarishChandra
