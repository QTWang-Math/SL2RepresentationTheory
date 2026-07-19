/-
Copyright (c) 2026 LieTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LieTheory contributors
-/
import LieTheory.SL2RHarishChandra.Support
import Mathlib.Algebra.Lie.Semisimple.Defs

/-! # Parity decomposition for algebraic `SL₂(ℝ)` modules -/

namespace LieTheory.SL2RHarishChandra

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
variable [LieRingModule sl2Compact M] [LieModule ℂ sl2Compact M]

/-- The sum of all K-types congruent to `r` modulo two. -/
def parityPart (r : ℤ) : Submodule ℂ M :=
  ⨆ n : {n : ℤ // n % 2 = r}, KWeightSpace M n.1

private theorem H_preserves_parityPart (r : ℤ) {v : M} (hv : v ∈ parityPart M r) :
    ⁅H, v⁆ ∈ parityPart M r := by
  refine Submodule.iSup_induction (fun n : {n : ℤ // n % 2 = r} => KWeightSpace M n.1)
    (motive := fun x => ⁅H, x⁆ ∈ parityPart M r) hv ?_ (by simp)
      (by intro x y hx hy; simpa [lie_add] using add_mem hx hy)
  intro n x hx
  have hxmem := hx
  rw [mem_KWeightSpace_iff] at hx
  rw [hx]
  exact (parityPart M r).smul_mem _ (Submodule.mem_iSup_of_mem n hxmem)

private theorem E_preserves_parityPart (r : ℤ) {v : M} (hv : v ∈ parityPart M r) :
    ⁅E, v⁆ ∈ parityPart M r := by
  refine Submodule.iSup_induction (fun n : {n : ℤ // n % 2 = r} => KWeightSpace M n.1)
    (motive := fun x => ⁅E, x⁆ ∈ parityPart M r) hv ?_ (by simp)
      (by intro x y hx hy; simpa [lie_add] using add_mem hx hy)
  intro n x hx
  apply Submodule.mem_iSup_of_mem
    (⟨n.1 + 2, by simpa [Int.add_emod] using n.2⟩ : {m : ℤ // m % 2 = r})
  exact E_mem_KWeightSpace M hx

private theorem F_preserves_parityPart (r : ℤ) {v : M} (hv : v ∈ parityPart M r) :
    ⁅F, v⁆ ∈ parityPart M r := by
  refine Submodule.iSup_induction (fun n : {n : ℤ // n % 2 = r} => KWeightSpace M n.1)
    (motive := fun x => ⁅F, x⁆ ∈ parityPart M r) hv ?_ (by simp)
      (by intro x y hx hy; simpa [lie_add] using add_mem hx hy)
  intro n x hx
  apply Submodule.mem_iSup_of_mem
    (⟨n.1 - 2, by simpa [Int.sub_emod] using n.2⟩ : {m : ℤ // m % 2 = r})
  exact F_mem_KWeightSpace M hx

/-- The weights of a fixed parity form an `sl₂Compact` Lie submodule. -/
def parityLieSubmodule (r : ℤ) : LieSubmodule ℂ sl2Compact M where
  __ := parityPart M r
  lie_mem := by
    intro X v hv
    rw [decompose X, add_lie, add_lie, smul_lie, smul_lie, smul_lie]
    exact add_mem (add_mem
      ((parityPart M r).smul_mem _ (H_preserves_parityPart M r hv))
      ((parityPart M r).smul_mem _ (E_preserves_parityPart M r hv)))
      ((parityPart M r).smul_mem _ (F_preserves_parityPart M r hv))

abbrev evenLieSubmodule : LieSubmodule ℂ sl2Compact M := parityLieSubmodule M 0
abbrev oddLieSubmodule : LieSubmodule ℂ sl2Compact M := parityLieSubmodule M 1

theorem even_disjoint_odd : Disjoint (parityPart M 0) (parityPart M 1) := by
  let s : Set ℤ := {n | n % 2 = 0}
  let t : Set ℤ := {n | n % 2 = 1}
  have hst : Disjoint s t := by
    rw [Set.disjoint_left]
    intro n hn0 hn1
    exact zero_ne_one (hn0.symm.trans hn1)
  have h := (kWeightSpaces_iSupIndep M).disjoint_biSup_biSup hst
  dsimp [s, t] at h
  have heq : parityPart M 0 = ⨆ n : ℤ, ⨆ (_ : n % 2 = 0), KWeightSpace M n := by
    unfold parityPart
    exact (iSup_subtype' (f := fun n (_ : n % 2 = 0) => KWeightSpace M n)).symm
  have hoq : parityPart M 1 = ⨆ n : ℤ, ⨆ (_ : n % 2 = 1), KWeightSpace M n := by
    unfold parityPart
    exact (iSup_subtype' (f := fun n (_ : n % 2 = 1) => KWeightSpace M n)).symm
  rw [heq, hoq]
  exact h

theorem even_sup_odd_eq_top (hK : IsKFinite M) :
    evenLieSubmodule M ⊔ oddLieSubmodule M = ⊤ := by
  apply top_unique
  change (⨆ n : ℤ, KWeightSpace M n) = ⊤ at hK
  calc
    ⊤ = ⨆ n : ℤ, KWeightSpace M n := hK.symm
    _ ≤ evenLieSubmodule M ⊔ oddLieSubmodule M := by
      apply iSup_le
      intro n
      rcases Int.emod_two_eq_zero_or_one n with hn | hn
      · exact le_sup_of_le_left
          (le_iSup (fun m : {m : ℤ // m % 2 = 0} => KWeightSpace M m.1) ⟨n, hn⟩)
      · exact le_sup_of_le_right
          (le_iSup (fun m : {m : ℤ // m % 2 = 1} => KWeightSpace M m.1) ⟨n, hn⟩)

theorem irreducible_even_or_odd [LieModule.IsIrreducible ℂ sl2Compact M]
    (hK : IsKFinite M) : evenLieSubmodule M = ⊤ ∨ oddLieSubmodule M = ⊤ := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (evenLieSubmodule M) with he | he
  · right
    have hsup := even_sup_odd_eq_top M hK
    simpa [he] using hsup
  · exact Or.inl he

theorem support_even_of_even_eq_top (he : evenLieSubmodule M = ⊤) {n : ℤ}
    (hn : n ∈ KSupport M) : n % 2 = 0 := by
  rcases Int.emod_two_eq_zero_or_one n with hzero | hone
  · exact hzero
  · exfalso
    rcases (mem_KSupport_iff_exists_weight_vector M n).mp hn with ⟨v, hv⟩
    have hve : (v : M) ∈ parityPart M 0 := by
      have : (v : M) ∈ evenLieSubmodule M := by rw [he]; exact Set.mem_univ _
      exact this
    have hvo : (v : M) ∈ parityPart M 1 :=
      Submodule.mem_iSup_of_mem (⟨n, hone⟩ : {m : ℤ // m % 2 = 1}) v.2
    have hb : (v : M) ∈ (⊥ : Submodule ℂ M) :=
      (disjoint_iff_inf_le.mp (even_disjoint_odd M)) ⟨hve, hvo⟩
    apply hv
    apply Subtype.ext
    exact (Submodule.mem_bot ℂ).mp hb

theorem support_odd_of_odd_eq_top (ho : oddLieSubmodule M = ⊤) {n : ℤ}
    (hn : n ∈ KSupport M) : n % 2 = 1 := by
  rcases Int.emod_two_eq_zero_or_one n with hzero | hone
  · exfalso
    rcases (mem_KSupport_iff_exists_weight_vector M n).mp hn with ⟨v, hv⟩
    have hve : (v : M) ∈ parityPart M 0 :=
      Submodule.mem_iSup_of_mem (⟨n, hzero⟩ : {m : ℤ // m % 2 = 0}) v.2
    have hvo : (v : M) ∈ parityPart M 1 := by
      have : (v : M) ∈ oddLieSubmodule M := by rw [ho]; exact Set.mem_univ _
      exact this
    have hb : (v : M) ∈ (⊥ : Submodule ℂ M) :=
      (disjoint_iff_inf_le.mp (even_disjoint_odd M)) ⟨hve, hvo⟩
    apply hv
    apply Subtype.ext
    exact (Submodule.mem_bot ℂ).mp hb
  · exact hone

theorem irreducible_support_has_fixed_parity [LieModule.IsIrreducible ℂ sl2Compact M]
    (hK : IsKFinite M) :
    (∀ n ∈ KSupport M, n % 2 = 0) ∨ (∀ n ∈ KSupport M, n % 2 = 1) := by
  rcases irreducible_even_or_odd M hK with he | ho
  · exact Or.inl fun _ hn => support_even_of_even_eq_top M he hn
  · exact Or.inr fun _ hn => support_odd_of_odd_eq_top M ho hn

end LieTheory.SL2RHarishChandra
