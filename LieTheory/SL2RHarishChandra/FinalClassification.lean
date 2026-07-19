/-
Copyright (c) 2026 LieTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LieTheory contributors
-/
import LieTheory.SL2RHarishChandra.ModelEquivalences

/-! # Final four-class theorem for `SL₂(ℝ)` at rho -/

namespace LieTheory.SL2RHarishChandra

noncomputable section

variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
variable [AddCommGroup B] [Module ℂ B]
variable [LieRingModule sl2Compact A] [LieModule ℂ sl2Compact A]
variable [LieRingModule sl2Compact B] [LieModule ℂ sl2Compact B]

theorem mem_KWeightSpace_map_equiv (e : A ≃ₗ⁅ℂ,sl2Compact⁆ B)
    {n : ℤ} {v : A} (hv : v ∈ KWeightSpace A n) :
    e v ∈ KWeightSpace B n := by
  rw [mem_KWeightSpace_iff] at hv ⊢
  calc
    ⁅H, e v⁆ = e ⁅H, v⁆ := (e.toLieModuleHom.map_lie H v).symm
    _ = e ((n : ℂ) • v) := congrArg e hv
    _ = (n : ℂ) • e v := map_smul e (n : ℂ) v

theorem KSupport_eq_of_equiv (e : A ≃ₗ⁅ℂ,sl2Compact⁆ B) :
    KSupport A = KSupport B := by
  ext n
  rw [mem_KSupport_iff_exists_weight_vector, mem_KSupport_iff_exists_weight_vector]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨⟨e v, mem_KWeightSpace_map_equiv e v.2⟩, ?_⟩
    intro hzero
    apply hv
    have hev : e (v : A) = 0 := congrArg Subtype.val hzero
    apply Subtype.ext
    apply e.injective
    simpa using hev
  · rintro ⟨v, hv⟩
    refine ⟨⟨e.symm v, mem_KWeightSpace_map_equiv e.symm v.2⟩, ?_⟩
    intro hzero
    apply hv
    have hev : e.symm (v : B) = 0 := congrArg Subtype.val hzero
    apply Subtype.ext
    apply e.symm.injective
    simpa using hev

theorem noEquiv_trivial_positive :
    ¬ Nonempty (TrivialHC ≃ₗ⁅ℂ,sl2Compact⁆ HolomorphicDiscreteHC) := by
  rintro ⟨e⟩
  have h0 : (0 : ℤ) ∈ KSupport TrivialHC := (trivial_support 0).mpr rfl
  rw [KSupport_eq_of_equiv e] at h0
  rcases (holomorphic_support 0).mp h0 with ⟨j, hj⟩
  omega

theorem noEquiv_trivial_negative :
    ¬ Nonempty (TrivialHC ≃ₗ⁅ℂ,sl2Compact⁆ AntiholomorphicDiscreteHC) := by
  rintro ⟨e⟩
  have h0 : (0 : ℤ) ∈ KSupport TrivialHC := (trivial_support 0).mpr rfl
  rw [KSupport_eq_of_equiv e] at h0
  rcases (antiholomorphic_support 0).mp h0 with ⟨j, hj⟩
  omega

theorem noEquiv_trivial_odd :
    ¬ Nonempty (TrivialHC ≃ₗ⁅ℂ,sl2Compact⁆ OddPrincipalHC) := by
  rintro ⟨e⟩
  have h0 : (0 : ℤ) ∈ KSupport TrivialHC := (trivial_support 0).mpr rfl
  rw [KSupport_eq_of_equiv e] at h0
  exact zero_ne_one ((oddPrincipal_support 0).mp h0)

theorem noEquiv_positive_negative :
    ¬ Nonempty (HolomorphicDiscreteHC ≃ₗ⁅ℂ,sl2Compact⁆ AntiholomorphicDiscreteHC) := by
  rintro ⟨e⟩
  have h2 : (2 : ℤ) ∈ KSupport HolomorphicDiscreteHC :=
    (holomorphic_support 2).mpr ⟨0, by norm_num⟩
  rw [KSupport_eq_of_equiv e] at h2
  rcases (antiholomorphic_support 2).mp h2 with ⟨j, hj⟩
  omega

theorem noEquiv_positive_odd :
    ¬ Nonempty (HolomorphicDiscreteHC ≃ₗ⁅ℂ,sl2Compact⁆ OddPrincipalHC) := by
  rintro ⟨e⟩
  have h2 : (2 : ℤ) ∈ KSupport HolomorphicDiscreteHC :=
    (holomorphic_support 2).mpr ⟨0, by norm_num⟩
  rw [KSupport_eq_of_equiv e] at h2
  have := (oddPrincipal_support 2).mp h2
  norm_num at this

theorem noEquiv_negative_odd :
    ¬ Nonempty (AntiholomorphicDiscreteHC ≃ₗ⁅ℂ,sl2Compact⁆ OddPrincipalHC) := by
  rintro ⟨e⟩
  have hm2 : (-2 : ℤ) ∈ KSupport AntiholomorphicDiscreteHC :=
    (antiholomorphic_support (-2)).mpr ⟨0, by norm_num⟩
  rw [KSupport_eq_of_equiv e] at hm2
  have := (oddPrincipal_support (-2)).mp hm2
  norm_num at this

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
variable [LieRingModule sl2Compact M] [LieModule ℂ sl2Compact M]

/-- What it means for `M` to belong to one of the four rho classes.  The
equivalence is a genuine Lie-module equivalence, not merely equality of
K-supports. -/
def ClassifiesAs (c : RhoIrrepClass) : Prop :=
  match c with
  | .trivial => Nonempty (M ≃ₗ⁅ℂ,sl2Compact⁆ TrivialHC)
  | .positiveDiscrete => Nonempty (M ≃ₗ⁅ℂ,sl2Compact⁆ HolomorphicDiscreteHC)
  | .negativeDiscrete => Nonempty (M ≃ₗ⁅ℂ,sl2Compact⁆ AntiholomorphicDiscreteHC)
  | .oddPrincipal => Nonempty (M ≃ₗ⁅ℂ,sl2Compact⁆ OddPrincipalHC)

theorem classification_exists [Nontrivial M] [LieModule.IsIrreducible ℂ sl2Compact M]
    (hHC : IsHarishChandraModule M) (hrho : HasRhoInfinitesimalCharacter M) :
    ∃ c, ClassifiesAs M c := by
  rcases exists_rho_seed M hHC.kFinite hrho with h | h | h | h
  · rcases h with ⟨v, hv⟩
    exact ⟨.trivial, ⟨(trivialEquivOfSeed M v hv).symm⟩⟩
  · rcases h with ⟨v, hv⟩
    exact ⟨.positiveDiscrete, ⟨(positiveEquivOfSeed M hrho v hv).symm⟩⟩
  · rcases h with ⟨v, hv⟩
    exact ⟨.negativeDiscrete, ⟨(negativeEquivOfSeed M hrho v hv).symm⟩⟩
  · rcases h with ⟨v, hv⟩
    exact ⟨.oddPrincipal, ⟨(oddEquivOfSeed M hrho v hv).symm⟩⟩

theorem classification_unique {c d : RhoIrrepClass}
    (hc : ClassifiesAs M c) (hd : ClassifiesAs M d) : c = d := by
  cases c <;> cases d
  · rfl
  · rcases hc with ⟨ec⟩; rcases hd with ⟨ed⟩
    exact (noEquiv_trivial_positive ⟨ec.symm.trans ed⟩).elim
  · rcases hc with ⟨ec⟩; rcases hd with ⟨ed⟩
    exact (noEquiv_trivial_negative ⟨ec.symm.trans ed⟩).elim
  · rcases hc with ⟨ec⟩; rcases hd with ⟨ed⟩
    exact (noEquiv_trivial_odd ⟨ec.symm.trans ed⟩).elim
  · rcases hc with ⟨ec⟩; rcases hd with ⟨ed⟩
    exact (noEquiv_trivial_positive ⟨ed.symm.trans ec⟩).elim
  · rfl
  · rcases hc with ⟨ec⟩; rcases hd with ⟨ed⟩
    exact (noEquiv_positive_negative ⟨ec.symm.trans ed⟩).elim
  · rcases hc with ⟨ec⟩; rcases hd with ⟨ed⟩
    exact (noEquiv_positive_odd ⟨ec.symm.trans ed⟩).elim
  · rcases hc with ⟨ec⟩; rcases hd with ⟨ed⟩
    exact (noEquiv_trivial_negative ⟨ed.symm.trans ec⟩).elim
  · rcases hc with ⟨ec⟩; rcases hd with ⟨ed⟩
    exact (noEquiv_positive_negative ⟨ed.symm.trans ec⟩).elim
  · rfl
  · rcases hc with ⟨ec⟩; rcases hd with ⟨ed⟩
    exact (noEquiv_negative_odd ⟨ec.symm.trans ed⟩).elim
  · rcases hc with ⟨ec⟩; rcases hd with ⟨ed⟩
    exact (noEquiv_trivial_odd ⟨ed.symm.trans ec⟩).elim
  · rcases hc with ⟨ec⟩; rcases hd with ⟨ed⟩
    exact (noEquiv_positive_odd ⟨ed.symm.trans ec⟩).elim
  · rcases hc with ⟨ec⟩; rcases hd with ⟨ed⟩
    exact (noEquiv_negative_odd ⟨ed.symm.trans ec⟩).elim
  · rfl

/-- **Algebraic classification for `SL₂(ℝ)` at infinitesimal character rho.**

Here rho is normalized by `C = H² + 2H + 4FE`, and the hypothesis says that
`C` acts by zero.  Thus the trivial module, the two algebraic discrete-series
modules, and the odd algebraic principal-series module are the four and only
four irreducible admissible K-finite modules. -/
theorem classify_irreducible_harishChandra_rho
    [Nontrivial M] [LieModule.IsIrreducible ℂ sl2Compact M]
    (hHC : IsHarishChandraModule M) (hrho : HasRhoInfinitesimalCharacter M) :
    ∃! c : RhoIrrepClass, ClassifiesAs M c := by
  rcases classification_exists M hHC hrho with ⟨c, hc⟩
  exact ⟨c, hc, fun d hd => classification_unique M hd hc⟩

def KWeightSpaceEquiv (e : A ≃ₗ⁅ℂ,sl2Compact⁆ B) (n : ℤ) :
    KWeightSpace A n ≃ₗ[ℂ] KWeightSpace B n where
  toFun v := ⟨e v, mem_KWeightSpace_map_equiv e v.2⟩
  invFun v := ⟨e.symm v, mem_KWeightSpace_map_equiv e.symm v.2⟩
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp
  left_inv v := by ext; simp
  right_inv v := by ext; simp

/-- Multiplicity one is a theorem, not part of the Harish--Chandra-module
definition. -/
theorem kType_multiplicity_one
    [Nontrivial M] [LieModule.IsIrreducible ℂ sl2Compact M]
    (hHC : IsHarishChandraModule M) (hrho : HasRhoInfinitesimalCharacter M)
    (n : ℤ) : Module.finrank ℂ (KWeightSpace M n) ≤ 1 := by
  rcases classification_exists M hHC hrho with ⟨c, hc⟩
  cases c with
  | trivial =>
      rcases hc with ⟨e⟩
      rw [(KWeightSpaceEquiv e n).finrank_eq]
      simpa using LinearMap.finrank_le_finrank_of_injective
        (Submodule.subtype_injective (KWeightSpace TrivialHC n))
  | positiveDiscrete =>
      rcases hc with ⟨e⟩
      rw [(KWeightSpaceEquiv e n).finrank_eq]
      exact finrank_KWeightSpace_diagonal_le_one positiveWeight positiveWeight_injective
        holomorphic_H_diagonal n
  | negativeDiscrete =>
      rcases hc with ⟨e⟩
      rw [(KWeightSpaceEquiv e n).finrank_eq]
      exact finrank_KWeightSpace_diagonal_le_one negativeWeight negativeWeight_injective
        antiholomorphic_H_diagonal n
  | oddPrincipal =>
      rcases hc with ⟨e⟩
      rw [(KWeightSpaceEquiv e n).finrank_eq]
      exact finrank_KWeightSpace_diagonal_le_one oddWeight oddWeight_injective
        oddPrincipal_H_diagonal n

/-- The support version of the classification, derived from the actual
module equivalence theorem. -/
theorem classify_KSupport
    [Nontrivial M] [LieModule.IsIrreducible ℂ sl2Compact M]
    (hHC : IsHarishChandraModule M) (hrho : HasRhoInfinitesimalCharacter M) :
    (∀ n, n ∈ KSupport M ↔ n = 0) ∨
    (∀ n, n ∈ KSupport M ↔ ∃ j : ℕ, n = 2 + 2 * (j : ℤ)) ∨
    (∀ n, n ∈ KSupport M ↔ ∃ j : ℕ, n = -2 - 2 * (j : ℤ)) ∨
    (∀ n, n ∈ KSupport M ↔ n % 2 = 1) := by
  rcases classification_exists M hHC hrho with ⟨c, hc⟩
  cases c with
  | trivial =>
      rcases hc with ⟨e⟩
      left
      intro n
      rw [KSupport_eq_of_equiv e, trivial_support]
  | positiveDiscrete =>
      rcases hc with ⟨e⟩
      right; left
      intro n
      rw [KSupport_eq_of_equiv e, holomorphic_support]
  | negativeDiscrete =>
      rcases hc with ⟨e⟩
      right; right; left
      intro n
      rw [KSupport_eq_of_equiv e, antiholomorphic_support]
  | oddPrincipal =>
      rcases hc with ⟨e⟩
      right; right; right
      intro n
      rw [KSupport_eq_of_equiv e, oddPrincipal_support]

end

end LieTheory.SL2RHarishChandra
