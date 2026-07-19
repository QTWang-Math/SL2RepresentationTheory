/-
Copyright (c) 2026 LieTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LieTheory contributors
-/
import LieTheory.Sl2Classification.HighestWeight

/-!
# Linear independence and the highest-weight basis

The members of an `sl₂` string are nonzero eigenvectors of `h` with pairwise
distinct eigenvalues. This gives linear independence without introducing any
additional spectral theory.
-/

namespace LieTheory.Sl2Classification

open LieModule Set Submodule

universe u v w

variable {K : Type u} {L : Type v} {M : Type w}
variable [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable {h e f : L} {t : IsSl2Triple h e f}

namespace HighestWeightVector

/-- The `h`-eigenvalue attached to an index in the finite highest-weight
string. -/
def eigenvalue (P : HighestWeightVector (K := K) (M := M) t)
    (i : Fin (P.weight + 1)) : K :=
  (P.weight : K) - 2 * (i : ℕ)

omit [LieAlgebra K L] [LieModule K L M] in
/-- Distinct positions in an `sl₂` string have distinct `h`-eigenvalues in
characteristic zero. -/
theorem eigenvalue_injective (P : HighestWeightVector (K := K) (M := M) t) :
    Function.Injective P.eigenvalue := by
  intro i j hij
  apply Fin.ext
  apply Nat.cast_injective (R := K)
  apply mul_left_cancel₀ (show (2 : K) ≠ 0 by norm_num)
  exact sub_right_injective hij

/-- The finite highest-weight string is linearly independent. -/
theorem string_linearIndependent (P : HighestWeightVector (K := K) (M := M) t) :
    LinearIndependent K (fun i : Fin (P.weight + 1) ↦ P.stringVector i) := by
  apply (toEnd K L M h).eigenvectors_linearIndependent' P.eigenvalue
    P.eigenvalue_injective
  intro i
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff,
    toEnd_apply_apply]
  exact ⟨P.lie_h_stringVector i,
    P.stringVector_ne_zero (Nat.lt_succ_iff.mp i.isLt)⟩

/-- The linear span of the finite highest-weight string. -/
def stringSpan (P : HighestWeightVector (K := K) (M := M) t) : Submodule K M :=
  Submodule.span K (Set.range fun i : Fin (P.weight + 1) ↦ P.stringVector i)

omit [CharZero K] in
private theorem lie_mem_stringSpan_of_generators
    (P : HighestWeightVector (K := K) (M := M) t) (x : L)
    (hx : ∀ i : Fin (P.weight + 1), ⁅x, P.stringVector i⁆ ∈ P.stringSpan)
    {m : M} (hm : m ∈ P.stringSpan) : ⁅x, m⁆ ∈ P.stringSpan := by
  induction hm using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hx i
  | zero => simp
  | add y z _ _ hy hz =>
      rw [lie_add]
      exact add_mem hy hz
  | smul a y _ hy =>
      rw [lie_smul]
      exact smul_mem _ a hy

omit [CharZero K] in
/-- The Cartan element `h` preserves the finite string span. -/
theorem lie_h_mem_stringSpan (P : HighestWeightVector (K := K) (M := M) t)
    {m : M} (hm : m ∈ P.stringSpan) : ⁅h, m⁆ ∈ P.stringSpan := by
  apply lie_mem_stringSpan_of_generators P h _ hm
  intro i
  rw [P.lie_h_stringVector]
  exact smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

omit [CharZero K] in
/-- The raising operator `e` preserves the finite string span. -/
theorem lie_e_mem_stringSpan (P : HighestWeightVector (K := K) (M := M) t)
    {m : M} (hm : m ∈ P.stringSpan) : ⁅e, m⁆ ∈ P.stringSpan := by
  apply lie_mem_stringSpan_of_generators P e _ hm
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change ⁅e, P.stringVector 0⁆ ∈ P.stringSpan
    rw [P.stringVector_zero, P.isPrimitive.lie_e]
    exact zero_mem _
  · change ⁅e, P.stringVector (j.val + 1)⁆ ∈ P.stringSpan
    rw [P.lie_e_stringVector_succ]
    exact smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j.castSucc))

/-- The lowering operator `f` preserves the finite string span, using the
vanishing of the vector immediately after its last member. -/
theorem lie_f_mem_stringSpan [FiniteDimensional K M]
    (P : HighestWeightVector (K := K) (M := M) t)
    {m : M} (hm : m ∈ P.stringSpan) : ⁅f, m⁆ ∈ P.stringSpan := by
  apply lie_mem_stringSpan_of_generators P f _ hm
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · change ⁅f, P.stringVector P.weight⁆ ∈ P.stringSpan
    rw [P.lie_f_stringVector, P.stringVector_succ_weight_eq_zero]
    exact zero_mem _
  · change ⁅f, P.stringVector j.val⁆ ∈ P.stringSpan
    rw [P.lie_f_stringVector]
    exact Submodule.subset_span (Set.mem_range_self j.succ)

/-- The finite string span as a Lie submodule. Closure under the whole ambient
Lie algebra follows because `h`, `e`, and `f` generate it. -/
def stringLieSubmodule [FiniteDimensional K M]
    (P : HighestWeightVector (K := K) (M := M) t) (hgen : IsGenerating (K := K) t) :
    LieSubmodule K L M where
  __ := P.stringSpan
  lie_mem := by
    intro x m hm
    have hx : x ∈ t.toLieSubalgebra K := by
      rw [hgen]
      exact Submodule.mem_top
    obtain ⟨a, b, c, rfl⟩ := IsSl2Triple.mem_toLieSubalgebra_iff.mp hx
    simp only [add_lie, smul_lie, t.lie_e_f]
    exact add_mem
      (add_mem (smul_mem _ a (P.lie_e_mem_stringSpan hm))
        (smul_mem _ b (P.lie_f_mem_stringSpan hm)))
      (smul_mem _ c (P.lie_h_mem_stringSpan hm))

@[simp]
theorem stringLieSubmodule_toSubmodule [FiniteDimensional K M]
    (P : HighestWeightVector (K := K) (M := M) t) (hgen : IsGenerating (K := K) t) :
    (P.stringLieSubmodule hgen : Submodule K M) = P.stringSpan :=
  rfl

/-- In an irreducible representation, the nonzero string Lie submodule is the
whole representation. -/
theorem stringLieSubmodule_eq_top [FiniteDimensional K M]
    [LieModule.IsIrreducible K L M]
    (P : HighestWeightVector (K := K) (M := M) t) (hgen : IsGenerating (K := K) t) :
    P.stringLieSubmodule hgen = ⊤ := by
  let N := P.stringLieSubmodule hgen
  have hmem : P.vector ∈ N := by
    change P.vector ∈ P.stringSpan
    rw [← P.stringVector_zero]
    exact Submodule.subset_span (Set.mem_range_self (0 : Fin (P.weight + 1)))
  have hne : N ≠ ⊥ := by
    intro hN
    apply P.isPrimitive.ne_zero
    exact LieSubmodule.mem_bot P.vector |>.mp (hN ▸ hmem)
  letI : Nontrivial N :=
    (LieSubmodule.nontrivial_iff_ne_bot K L M).mpr hne
  exact LieSubmodule.eq_top_of_isIrreducible K L M N

/-- Consequently, the underlying linear span of the finite string is all of
`M`. -/
theorem stringSpan_eq_top [FiniteDimensional K M] [LieModule.IsIrreducible K L M]
    (P : HighestWeightVector (K := K) (M := M) t) (hgen : IsGenerating (K := K) t) :
    P.stringSpan = ⊤ := by
  have h := congrArg (fun N : LieSubmodule K L M ↦ (N : Submodule K M))
    (P.stringLieSubmodule_eq_top hgen)
  simpa using h

/-- The highest-weight string, promoted to a basis of an irreducible module. -/
noncomputable def stringBasis [FiniteDimensional K M] [LieModule.IsIrreducible K L M]
    (P : HighestWeightVector (K := K) (M := M) t) (hgen : IsGenerating (K := K) t) :
    Module.Basis (Fin (P.weight + 1)) K M :=
  Module.Basis.mk P.string_linearIndependent (P.stringSpan_eq_top hgen).ge

@[simp]
theorem stringBasis_apply [FiniteDimensional K M] [LieModule.IsIrreducible K L M]
    (P : HighestWeightVector (K := K) (M := M) t) (hgen : IsGenerating (K := K) t)
    (i : Fin (P.weight + 1)) :
    P.stringBasis hgen i = P.stringVector i := by
  apply Module.Basis.mk_apply

/-- The dimension of an irreducible module is one more than its highest
weight. -/
theorem finrank_eq_weight_add_one [FiniteDimensional K M]
    [LieModule.IsIrreducible K L M]
    (P : HighestWeightVector (K := K) (M := M) t) (hgen : IsGenerating (K := K) t) :
    Module.finrank K M = P.weight + 1 := by
  simpa using Module.finrank_eq_card_basis (P.stringBasis hgen)

end HighestWeightVector

/-- The standard action formulas for a highest-weight basis indexed by
`Fin (n + 1)`. -/
structure IsHighestWeightBasis (t : IsSl2Triple h e f) (n : ℕ)
    (b : Module.Basis (Fin (n + 1)) K M) : Prop where
  lie_h : ∀ i, ⁅h, b i⁆ = ((n : K) - 2 * (i : ℕ)) • b i
  lie_e_zero : ⁅e, b 0⁆ = 0
  lie_e_succ : ∀ i : Fin n,
    ⁅e, b i.succ⁆ =
      ((((i : ℕ) : K) + 1) * ((n : K) - (i : ℕ))) • b i.castSucc
  lie_f_castSucc : ∀ i : Fin n, ⁅f, b i.castSucc⁆ = b i.succ
  lie_f_last : ⁅f, b (Fin.last n)⁆ = 0

/-- There exists a basis with the standard highest-weight-`n` action
formulas. -/
def HasHighestWeightBasis (t : IsSl2Triple h e f) (n : ℕ) : Prop :=
  ∃ b : Module.Basis (Fin (n + 1)) K M, IsHighestWeightBasis t n b

namespace HighestWeightVector

/-- The string basis satisfies all standard `sl₂` action formulas. -/
theorem isHighestWeightBasis [FiniteDimensional K M] [LieModule.IsIrreducible K L M]
    (P : HighestWeightVector (K := K) (M := M) t) (hgen : IsGenerating (K := K) t) :
    IsHighestWeightBasis t P.weight (P.stringBasis hgen) where
  lie_h i := by
    simpa only [P.stringBasis_apply] using P.lie_h_stringVector (i : ℕ)
  lie_e_zero := by
    simp only [P.stringBasis_apply]
    change ⁅e, P.stringVector 0⁆ = 0
    simpa only [P.stringVector_zero] using P.isPrimitive.lie_e
  lie_e_succ i := by
    simp only [P.stringBasis_apply]
    change ⁅e, P.stringVector (i.val + 1)⁆ =
      ((((i.val : K) + 1) * ((P.weight : K) - i.val))) • P.stringVector i.val
    exact P.lie_e_stringVector_succ i.val
  lie_f_castSucc i := by
    simp only [P.stringBasis_apply]
    change ⁅f, P.stringVector i.val⁆ = P.stringVector (i.val + 1)
    exact P.lie_f_stringVector i.val
  lie_f_last := by
    simp only [P.stringBasis_apply]
    change ⁅f, P.stringVector P.weight⁆ = 0
    rw [P.lie_f_stringVector, P.stringVector_succ_weight_eq_zero]

end HighestWeightVector

/-- A finite-dimensional irreducible representation has a highest-weight
basis. -/
theorem exists_highestWeightBasis [IsAlgClosed K] [Nontrivial M]
    [FiniteDimensional K M] [LieModule.IsIrreducible K L M]
    (t : IsSl2Triple h e f) (hgen : IsGenerating (K := K) t) :
    ∃ n : ℕ, HasHighestWeightBasis (K := K) (M := M) t n := by
  obtain ⟨P⟩ := HighestWeightVector.exists_highestWeightVector
    (K := K) (M := M) (t := t)
  exact ⟨P.weight, P.stringBasis hgen, P.isHighestWeightBasis hgen⟩

omit [CharZero K] [LieAlgebra K L] [LieModule K L M] in
/-- The dimension of a module admitting a highest-weight-`n` basis is
`n + 1`. -/
theorem finrank_eq_add_one_of_hasHighestWeightBasis {n : ℕ}
    (H : HasHighestWeightBasis (K := K) (M := M) t n) :
    Module.finrank K M = n + 1 := by
  obtain ⟨b, -⟩ := H
  simpa using Module.finrank_eq_card_basis b

omit [CharZero K] [LieAlgebra K L] [LieModule K L M] in
/-- The highest weight is unique: it is determined by the dimension. -/
theorem highestWeight_unique {n m : ℕ}
    (hn : HasHighestWeightBasis (K := K) (M := M) t n)
    (hm : HasHighestWeightBasis (K := K) (M := M) t m) : n = m := by
  have hn' := finrank_eq_add_one_of_hasHighestWeightBasis hn
  have hm' := finrank_eq_add_one_of_hasHighestWeightBasis hm
  omega

/-- Core finite-dimensional irreducible `sl₂` classification theorem in
highest-weight-basis form. -/
theorem exists_unique_highestWeight_basis [IsAlgClosed K] [Nontrivial M]
    [FiniteDimensional K M] [LieModule.IsIrreducible K L M]
    (t : IsSl2Triple h e f) (hgen : IsGenerating (K := K) t) :
    ∃! n : ℕ, HasHighestWeightBasis (K := K) (M := M) t n := by
  obtain ⟨n, hn⟩ := exists_highestWeightBasis (K := K) (M := M) t hgen
  refine ⟨n, hn, ?_⟩
  intro m hm
  exact (highestWeight_unique (K := K) (M := M) hn hm).symm

end LieTheory.Sl2Classification
