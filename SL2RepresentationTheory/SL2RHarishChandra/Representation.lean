/-
Copyright (c) 2026 SL2RepresentationTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SL2RepresentationTheory contributors
-/
import SL2RepresentationTheory.SL2RHarishChandra.Parity

/-! # Building representations of the fixed `sl₂Compact` from three operators -/

namespace SL2RepresentationTheory.SL2RHarishChandra

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

local instance : LieRing (Module.End ℂ V) := LieRing.ofAssociativeRing

/-- The linear map determined by the images of the fixed basis `H`, `E`, `F`. -/
def operatorMapLinear (h e f : Module.End ℂ V) :
    sl2Compact →ₗ[ℂ] Module.End ℂ V where
  toFun X := X.1 0 0 • h + X.1 0 1 • e + X.1 1 0 • f
  map_add' X Y := by
    ext v
    simp [add_smul]
    module
  map_smul' c X := by
    ext v
    simp [mul_smul]

@[simp] theorem operatorMapLinear_H (h e f : Module.End ℂ V) :
    operatorMapLinear h e f H = h := by
  ext v
  simp [operatorMapLinear]

@[simp] theorem operatorMapLinear_E (h e f : Module.End ℂ V) :
    operatorMapLinear h e f E = e := by
  ext v
  simp [operatorMapLinear]

@[simp] theorem operatorMapLinear_F (h e f : Module.End ℂ V) :
    operatorMapLinear h e f F = f := by
  ext v
  simp [operatorMapLinear]

/-- Three operators satisfying the fixed `sl₂` relations define a
representation of the concrete complexified Lie algebra of `SL₂(ℝ)`. -/
def sl2LieHomOfOperators (h e f : Module.End ℂ V)
    (hhe : ⁅h, e⁆ = (2 : ℂ) • e)
    (hhf : ⁅h, f⁆ = -((2 : ℂ) • f))
    (hef : ⁅e, f⁆ = h) :
    sl2Compact →ₗ⁅ℂ⁆ Module.End ℂ V where
  __ := operatorMapLinear h e f
  map_lie' := by
    intro X Y
    ext v
    have hXtrace : X.1 0 0 + X.1 1 1 = 0 := by
      have hX := X.2
      change Matrix.trace X.1 = 0 at hX
      simpa [Matrix.trace, Fin.sum_univ_two] using hX
    have hYtrace : Y.1 0 0 + Y.1 1 1 = 0 := by
      have hY := Y.2
      change Matrix.trace Y.1 = 0 at hY
      simpa [Matrix.trace, Fin.sum_univ_two] using hY
    have hXdiag : X.1 1 1 = -X.1 0 0 := by linear_combination hXtrace
    have hYdiag : Y.1 1 1 = -Y.1 0 0 := by linear_combination hYtrace
    have hhe_v := LinearMap.congr_fun hhe v
    have hhf_v := LinearMap.congr_fun hhf v
    have hef_v := LinearMap.congr_fun hef v
    simp only [Ring.lie_def, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.neg_apply] at hhe_v hhf_v hef_v
    simp only [operatorMapLinear, LieAlgebra.SpecialLinear.sl_bracket,
      Ring.lie_def, LinearMap.add_apply, LinearMap.smul_apply]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [map_add, map_smul]
    rw [sub_eq_iff_eq_add.mp hhe_v, sub_eq_iff_eq_add.mp hhf_v,
      sub_eq_iff_eq_add.mp hef_v]
    rw [hXdiag, hYdiag]
    module

end SL2RepresentationTheory.SL2RHarishChandra
