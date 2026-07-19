/-
Copyright (c) 2026 LieTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LieTheory contributors
-/
import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Data.Complex.Basic

/-!
# The compact-normalized basis for `SL₂(ℝ)`

This file fixes the complexified Lie algebra of `SL₂(ℝ)` once and for all as
the trace-zero `2 × 2` complex matrices.  We use the normalized basis `H`, `E`,
and `F` satisfying

* `[H, E] = 2 E`,
* `[H, F] = -2 F`,
* `[E, F] = H`.

The element `H` is the algebraic normalization of the complexified compact
Cartan generator.  No topology, real Lie group action, or analytic
representation is introduced here.
-/

namespace LieTheory.SL2RHarishChandra

open Matrix

/-- The complexified Lie algebra used for the algebraic Harish--Chandra pair
of `SL₂(ℝ)`. -/
abbrev sl2Compact := LieAlgebra.SpecialLinear.sl (Fin 2) ℂ

/-- The normalized complexified compact Cartan generator. -/
def H : sl2Compact :=
  LieAlgebra.SpecialLinear.singleSubSingle (0 : Fin 2) (1 : Fin 2) 1

/-- The operator raising an integral `SO(2)` weight by two. -/
def E : sl2Compact :=
  LieAlgebra.SpecialLinear.single (0 : Fin 2) (1 : Fin 2) (by decide) 1

/-- The operator lowering an integral `SO(2)` weight by two. -/
def F : sl2Compact :=
  LieAlgebra.SpecialLinear.single (1 : Fin 2) (0 : Fin 2) (by decide) 1

@[simp]
theorem H_apply (i j : Fin 2) :
    (H : Matrix (Fin 2) (Fin 2) ℂ) i j =
      if i = 0 ∧ j = 0 then 1 else if i = 1 ∧ j = 1 then -1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [H, Matrix.single]

@[simp]
theorem E_apply (i j : Fin 2) :
    (E : Matrix (Fin 2) (Fin 2) ℂ) i j = if i = 0 ∧ j = 1 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [E, Matrix.single]

@[simp]
theorem F_apply (i j : Fin 2) :
    (F : Matrix (Fin 2) (Fin 2) ℂ) i j = if i = 1 ∧ j = 0 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [F, Matrix.single]

theorem H_ne_zero : H ≠ 0 := by
  intro h
  have h00 := congrArg (fun X : sl2Compact => (X : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num at h00

theorem lie_H_E : ⁅H, E⁆ = (2 : ℂ) • E := by
  apply Subtype.ext
  rw [LieAlgebra.SpecialLinear.sl_bracket]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply]

theorem lie_H_F : ⁅H, F⁆ = -((2 : ℂ) • F) := by
  apply Subtype.ext
  rw [LieAlgebra.SpecialLinear.sl_bracket]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply]

theorem lie_E_F : ⁅E, F⁆ = H := by
  apply Subtype.ext
  rw [LieAlgebra.SpecialLinear.sl_bracket]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply]

/-- The fixed normalized `sl₂` triple for the algebraic Harish--Chandra pair
of `SL₂(ℝ)`. -/
theorem isSl2Triple : IsSl2Triple H E F where
  h_ne_zero := H_ne_zero
  lie_e_f := lie_E_F
  lie_h_e_nsmul := by simpa [two_smul] using lie_H_E
  lie_h_f_nsmul := by simpa [two_smul] using lie_H_F

/-- Entrywise decomposition of a trace-zero `2 × 2` matrix in the fixed
`H`, `E`, `F` basis. -/
theorem decompose (X : sl2Compact) :
    X = (X.1 0 0) • H + (X.1 0 1) • E + (X.1 1 0) • F := by
  have htrace : X.1 0 0 + X.1 1 1 = 0 := by
    have hX := X.2
    change Matrix.trace X.1 = 0 at hX
    simpa [Matrix.trace, Fin.sum_univ_two] using hX
  have hdiag : X.1 1 1 = -X.1 0 0 := by
    linear_combination htrace
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hdiag]

/-- The fixed three elements span, hence generate, the full complexified Lie
algebra of `SL₂(ℝ)`. -/
theorem toLieSubalgebra_eq_top : isSl2Triple.toLieSubalgebra ℂ = ⊤ := by
  apply top_unique
  intro X _
  rw [IsSl2Triple.mem_toLieSubalgebra_iff]
  refine ⟨X.1 0 1, X.1 1 0, X.1 0 0, ?_⟩
  rw [lie_E_F]
  simpa [add_assoc, add_left_comm, add_comm] using decompose X

end LieTheory.SL2RHarishChandra
