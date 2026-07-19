/-
Copyright (c) 2026 LieTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LieTheory contributors
-/
import LieTheory.SL2RHarishChandra.Representation
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # The four algebraic rho-infinitesimal-character models for `SL₂(ℝ)` -/

namespace LieTheory.SL2RHarishChandra

inductive RhoIrrepClass
  | trivial
  | positiveDiscrete
  | negativeDiscrete
  | oddPrincipal
  deriving DecidableEq, Repr

abbrev TrivialHC := ℂ
abbrev HolomorphicDiscreteHC := ℕ →₀ ℂ
/-- A tagged copy of `ℕ`, used so that the positive and negative discrete
models carry genuinely distinct typeclass instances. -/
abbrev NegativeIndex := ULift.{0, 0} ℕ
abbrev AntiholomorphicDiscreteHC := NegativeIndex →₀ ℂ
abbrev OddPrincipalHC := ℤ →₀ ℂ

noncomputable section

variable {ι : Type*}

/-- Extend prescribed images of the standard Finsupp basis linearly. -/
def finsuppEndOfBasis (b : ι → ι →₀ ℂ) : Module.End ℂ (ι →₀ ℂ) :=
  (Finsupp.basisSingleOne.constr ℂ b : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ))

@[simp] theorem finsuppEndOfBasis_single (b : ι → ι →₀ ℂ) (i : ι) :
    finsuppEndOfBasis b (Finsupp.single i 1) = b i := by
  simpa [finsuppEndOfBasis] using Finsupp.basisSingleOne.constr_basis ℂ b i

@[simp] theorem finsuppEndOfBasis_single_apply (b : ι → ι →₀ ℂ) (i : ι) (c : ℂ) :
    finsuppEndOfBasis b (Finsupp.single i c) = c • b i := by
  have h := (finsuppEndOfBasis b).map_smul c (Finsupp.single i 1)
  simpa using h

def positiveH : Module.End ℂ HolomorphicDiscreteHC :=
  finsuppEndOfBasis fun j => Finsupp.single j (2 + 2 * (j : ℂ))

def positiveE : Module.End ℂ HolomorphicDiscreteHC :=
  finsuppEndOfBasis fun j => Finsupp.single (j + 1) 1

def positiveFImage : ℕ → HolomorphicDiscreteHC
  | 0 => 0
  | j + 1 => Finsupp.single j (-((j + 1 : ℕ) : ℂ) * ((j + 2 : ℕ) : ℂ))

def positiveF : Module.End ℂ HolomorphicDiscreteHC :=
  finsuppEndOfBasis positiveFImage

local instance {V : Type*} [AddCommGroup V] [Module ℂ V] : LieRing (Module.End ℂ V) :=
  LieRing.ofAssociativeRing

theorem positive_lie_H_E : ⁅positiveH, positiveE⁆ = (2 : ℂ) • positiveE := by
  apply Finsupp.basisSingleOne.ext
  intro j
  simp [positiveH, positiveE, Ring.lie_def, Module.End.mul_apply]
  ext i
  simp [Finsupp.single_apply]
  split_ifs <;> ring

theorem positive_lie_H_F : ⁅positiveH, positiveF⁆ = -((2 : ℂ) • positiveF) := by
  apply Finsupp.basisSingleOne.ext
  intro j
  cases j with
  | zero => simp [positiveH, positiveF, positiveFImage, Ring.lie_def, Module.End.mul_apply]
  | succ j =>
      simp [positiveH, positiveF, positiveFImage, Ring.lie_def, Module.End.mul_apply]
      ext i
      simp [Finsupp.single_apply]
      split_ifs <;> ring

theorem positive_lie_E_F : ⁅positiveE, positiveF⁆ = positiveH := by
  apply Finsupp.basisSingleOne.ext
  intro j
  cases j with
  | zero => simp [positiveH, positiveE, positiveF, positiveFImage, Ring.lie_def,
      Module.End.mul_apply]
  | succ j =>
      simp [positiveH, positiveE, positiveF, positiveFImage, Ring.lie_def,
        Module.End.mul_apply]
      ext i
      simp [Finsupp.single_apply]
      split_ifs <;> ring

def positiveRepresentation : sl2Compact →ₗ⁅ℂ⁆ Module.End ℂ HolomorphicDiscreteHC :=
  sl2LieHomOfOperators positiveH positiveE positiveF
    positive_lie_H_E positive_lie_H_F positive_lie_E_F

noncomputable instance holomorphicLieRingModule :
    LieRingModule sl2Compact HolomorphicDiscreteHC :=
  LieRingModule.compLieHom HolomorphicDiscreteHC positiveRepresentation

noncomputable instance holomorphicLieModule :
    LieModule ℂ sl2Compact HolomorphicDiscreteHC :=
  LieModule.compLieHom HolomorphicDiscreteHC positiveRepresentation

theorem holomorphic_toEnd_H :
    LieModule.toEnd ℂ sl2Compact HolomorphicDiscreteHC H = positiveH := by
  apply LinearMap.ext
  intro v
  change positiveRepresentation H v = positiveH v
  simp [positiveRepresentation, sl2LieHomOfOperators, operatorMapLinear]

theorem holomorphic_toEnd_E :
    LieModule.toEnd ℂ sl2Compact HolomorphicDiscreteHC E = positiveE := by
  apply LinearMap.ext
  intro v
  change positiveRepresentation E v = positiveE v
  simp [positiveRepresentation, sl2LieHomOfOperators, operatorMapLinear]

theorem holomorphic_toEnd_F :
    LieModule.toEnd ℂ sl2Compact HolomorphicDiscreteHC F = positiveF := by
  apply LinearMap.ext
  intro v
  change positiveRepresentation F v = positiveF v
  simp [positiveRepresentation, sl2LieHomOfOperators, operatorMapLinear]

@[simp] theorem holomorphic_H_single (j : ℕ) :
    ⁅H, (Finsupp.single j 1 : HolomorphicDiscreteHC)⁆ =
      Finsupp.single j (2 + 2 * (j : ℂ)) := by
  change positiveRepresentation H (Finsupp.single j 1) = _
  simp [positiveRepresentation, sl2LieHomOfOperators, operatorMapLinear, positiveH]

@[simp] theorem holomorphic_E_single (j : ℕ) :
    ⁅E, (Finsupp.single j 1 : HolomorphicDiscreteHC)⁆ = Finsupp.single (j + 1) 1 := by
  change positiveRepresentation E (Finsupp.single j 1) = _
  simp [positiveRepresentation, sl2LieHomOfOperators, operatorMapLinear, positiveE]

@[simp] theorem holomorphic_F_single (j : ℕ) :
    ⁅F, (Finsupp.single j 1 : HolomorphicDiscreteHC)⁆ = positiveFImage j := by
  change positiveRepresentation F (Finsupp.single j 1) = _
  simp [positiveRepresentation, sl2LieHomOfOperators, operatorMapLinear, positiveF]

theorem holomorphic_hasRhoInfinitesimalCharacter :
    HasRhoInfinitesimalCharacter HolomorphicDiscreteHC := by
  unfold HasRhoInfinitesimalCharacter
  apply Finsupp.basisSingleOne.ext
  intro j
  rw [Finsupp.coe_basisSingleOne]
  unfold casimirAction HAction EAction FAction
  rw [holomorphic_toEnd_H, holomorphic_toEnd_E, holomorphic_toEnd_F]
  simp only [Pi.zero_apply]
  change (positiveH * positiveH + 2 • positiveH + 4 • (positiveF * positiveE))
    (Finsupp.single j 1) = 0
  simp [positiveH, positiveE, positiveF, positiveFImage]
  ext i
  simp [Finsupp.single_apply]
  split_ifs <;> ring

def negativeH : Module.End ℂ AntiholomorphicDiscreteHC :=
  finsuppEndOfBasis fun j => Finsupp.single j (-2 - 2 * (j.down : ℂ))

def negativeF : Module.End ℂ AntiholomorphicDiscreteHC :=
  finsuppEndOfBasis fun j => Finsupp.single (ULift.up (j.down + 1)) 1

def negativeEImage (j : NegativeIndex) : AntiholomorphicDiscreteHC :=
  match j.down with
  | 0 => 0
  | k + 1 => Finsupp.single (ULift.up k) (-((k + 1 : ℕ) : ℂ) * ((k + 2 : ℕ) : ℂ))

def negativeE : Module.End ℂ AntiholomorphicDiscreteHC :=
  finsuppEndOfBasis negativeEImage

theorem negative_lie_H_E : ⁅negativeH, negativeE⁆ = (2 : ℂ) • negativeE := by
  apply Finsupp.basisSingleOne.ext
  rintro ⟨j⟩
  cases j with
  | zero => simp [negativeH, negativeE, negativeEImage]
  | succ j =>
      simp [negativeH, negativeE, negativeEImage]
      ext i
      simp [Finsupp.single_apply]
      split_ifs <;> ring

theorem negative_lie_H_F : ⁅negativeH, negativeF⁆ = -((2 : ℂ) • negativeF) := by
  apply Finsupp.basisSingleOne.ext
  rintro ⟨j⟩
  simp [negativeH, negativeF]
  ext i
  simp [Finsupp.single_apply]
  split_ifs <;> ring

theorem negative_lie_E_F : ⁅negativeE, negativeF⁆ = negativeH := by
  apply Finsupp.basisSingleOne.ext
  rintro ⟨j⟩
  cases j with
  | zero => simp [negativeH, negativeE, negativeF, negativeEImage]
  | succ j =>
      simp [negativeH, negativeE, negativeF, negativeEImage]
      ext i
      simp [Finsupp.single_apply]
      split_ifs <;> ring

def negativeRepresentation : sl2Compact →ₗ⁅ℂ⁆ Module.End ℂ AntiholomorphicDiscreteHC :=
  sl2LieHomOfOperators negativeH negativeE negativeF
    negative_lie_H_E negative_lie_H_F negative_lie_E_F

noncomputable instance antiholomorphicLieRingModule :
    LieRingModule sl2Compact AntiholomorphicDiscreteHC :=
  LieRingModule.compLieHom AntiholomorphicDiscreteHC negativeRepresentation

noncomputable instance antiholomorphicLieModule :
    LieModule ℂ sl2Compact AntiholomorphicDiscreteHC :=
  LieModule.compLieHom AntiholomorphicDiscreteHC negativeRepresentation

theorem antiholomorphic_toEnd_H :
    LieModule.toEnd ℂ sl2Compact AntiholomorphicDiscreteHC H = negativeH := by
  apply LinearMap.ext; intro v
  change negativeRepresentation H v = negativeH v
  simp [negativeRepresentation, sl2LieHomOfOperators, operatorMapLinear]

theorem antiholomorphic_toEnd_E :
    LieModule.toEnd ℂ sl2Compact AntiholomorphicDiscreteHC E = negativeE := by
  apply LinearMap.ext; intro v
  change negativeRepresentation E v = negativeE v
  simp [negativeRepresentation, sl2LieHomOfOperators, operatorMapLinear]

theorem antiholomorphic_toEnd_F :
    LieModule.toEnd ℂ sl2Compact AntiholomorphicDiscreteHC F = negativeF := by
  apply LinearMap.ext; intro v
  change negativeRepresentation F v = negativeF v
  simp [negativeRepresentation, sl2LieHomOfOperators, operatorMapLinear]

@[simp] theorem antiholomorphic_E_single (j : NegativeIndex) :
    ⁅E, (Finsupp.single j 1 : AntiholomorphicDiscreteHC)⁆ = negativeEImage j := by
  change negativeRepresentation E (Finsupp.single j 1) = _
  simp [negativeRepresentation, sl2LieHomOfOperators, operatorMapLinear, negativeE]

@[simp] theorem antiholomorphic_F_single (j : NegativeIndex) :
    ⁅F, (Finsupp.single j 1 : AntiholomorphicDiscreteHC)⁆ =
      Finsupp.single (ULift.up (j.down + 1)) 1 := by
  change negativeRepresentation F (Finsupp.single j 1) = _
  simp [negativeRepresentation, sl2LieHomOfOperators, operatorMapLinear, negativeF]

theorem antiholomorphic_hasRhoInfinitesimalCharacter :
    HasRhoInfinitesimalCharacter AntiholomorphicDiscreteHC := by
  unfold HasRhoInfinitesimalCharacter casimirAction HAction EAction FAction
  rw [antiholomorphic_toEnd_H, antiholomorphic_toEnd_E, antiholomorphic_toEnd_F]
  apply Finsupp.basisSingleOne.ext
  rintro ⟨j⟩
  rw [Finsupp.coe_basisSingleOne]
  cases j with
  | zero => simp [negativeH, negativeE, negativeF, negativeEImage]
  | succ j =>
      simp [negativeH, negativeE, negativeF, negativeEImage]
      ext i
      simp [Finsupp.single_apply]
      split_ifs <;> ring

def oddH : Module.End ℂ OddPrincipalHC :=
  finsuppEndOfBasis fun j => Finsupp.single j (2 * (j : ℂ) + 1)

def oddE : Module.End ℂ OddPrincipalHC :=
  finsuppEndOfBasis fun j => Finsupp.single (j + 1) 1

def oddF : Module.End ℂ OddPrincipalHC :=
  finsuppEndOfBasis fun j =>
    Finsupp.single (j - 1) ((1 - 4 * (j : ℂ) ^ 2) / 4)

theorem odd_lie_H_E : ⁅oddH, oddE⁆ = (2 : ℂ) • oddE := by
  apply Finsupp.basisSingleOne.ext
  intro j
  simp [oddH, oddE]
  ext i
  simp [Finsupp.single_apply]
  split_ifs <;> ring

theorem odd_lie_H_F : ⁅oddH, oddF⁆ = -((2 : ℂ) • oddF) := by
  apply Finsupp.basisSingleOne.ext
  intro j
  simp [oddH, oddF]
  ext i
  simp [Finsupp.single_apply]
  split_ifs <;> ring

theorem odd_lie_E_F : ⁅oddE, oddF⁆ = oddH := by
  apply Finsupp.basisSingleOne.ext
  intro j
  simp [oddH, oddE, oddF]
  ext i
  simp [Finsupp.single_apply]
  split_ifs <;> ring

def oddRepresentation : sl2Compact →ₗ⁅ℂ⁆ Module.End ℂ OddPrincipalHC :=
  sl2LieHomOfOperators oddH oddE oddF odd_lie_H_E odd_lie_H_F odd_lie_E_F

noncomputable instance oddPrincipalLieRingModule : LieRingModule sl2Compact OddPrincipalHC :=
  LieRingModule.compLieHom OddPrincipalHC oddRepresentation

noncomputable instance oddPrincipalLieModule : LieModule ℂ sl2Compact OddPrincipalHC :=
  LieModule.compLieHom OddPrincipalHC oddRepresentation

theorem oddPrincipal_toEnd_H :
    LieModule.toEnd ℂ sl2Compact OddPrincipalHC H = oddH := by
  apply LinearMap.ext; intro v
  change oddRepresentation H v = oddH v
  simp [oddRepresentation, sl2LieHomOfOperators, operatorMapLinear]

theorem oddPrincipal_toEnd_E :
    LieModule.toEnd ℂ sl2Compact OddPrincipalHC E = oddE := by
  apply LinearMap.ext; intro v
  change oddRepresentation E v = oddE v
  simp [oddRepresentation, sl2LieHomOfOperators, operatorMapLinear]

theorem oddPrincipal_toEnd_F :
    LieModule.toEnd ℂ sl2Compact OddPrincipalHC F = oddF := by
  apply LinearMap.ext; intro v
  change oddRepresentation F v = oddF v
  simp [oddRepresentation, sl2LieHomOfOperators, operatorMapLinear]

@[simp] theorem oddPrincipal_E_single (j : ℤ) :
    ⁅E, (Finsupp.single j 1 : OddPrincipalHC)⁆ = Finsupp.single (j + 1) 1 := by
  change oddRepresentation E (Finsupp.single j 1) = _
  simp [oddRepresentation, sl2LieHomOfOperators, operatorMapLinear, oddE]

@[simp] theorem oddPrincipal_F_single (j : ℤ) :
    ⁅F, (Finsupp.single j 1 : OddPrincipalHC)⁆ =
      Finsupp.single (j - 1) ((1 - 4 * (j : ℂ) ^ 2) / 4) := by
  change oddRepresentation F (Finsupp.single j 1) = _
  simp [oddRepresentation, sl2LieHomOfOperators, operatorMapLinear, oddF]

theorem oddPrincipal_hasRhoInfinitesimalCharacter :
    HasRhoInfinitesimalCharacter OddPrincipalHC := by
  unfold HasRhoInfinitesimalCharacter casimirAction HAction EAction FAction
  rw [oddPrincipal_toEnd_H, oddPrincipal_toEnd_E, oddPrincipal_toEnd_F]
  apply Finsupp.basisSingleOne.ext
  intro j
  rw [Finsupp.coe_basisSingleOne]
  simp [oddH, oddE, oddF]
  ext i
  simp [Finsupp.single_apply]
  split_ifs <;> ring

def trivialRepresentation : sl2Compact →ₗ⁅ℂ⁆ Module.End ℂ TrivialHC :=
  sl2LieHomOfOperators 0 0 0 (by simp) (by simp) (by simp)

noncomputable instance trivialHCLieRingModule : LieRingModule sl2Compact TrivialHC :=
  LieRingModule.compLieHom TrivialHC trivialRepresentation

noncomputable instance trivialHCLieModule : LieModule ℂ sl2Compact TrivialHC :=
  LieModule.compLieHom TrivialHC trivialRepresentation

theorem trivial_toEnd (X : sl2Compact) :
    LieModule.toEnd ℂ sl2Compact TrivialHC X = 0 := by
  apply LinearMap.ext
  intro v
  change trivialRepresentation X v = 0
  simp [trivialRepresentation, sl2LieHomOfOperators, operatorMapLinear]

theorem trivial_hasRhoInfinitesimalCharacter : HasRhoInfinitesimalCharacter TrivialHC := by
  unfold HasRhoInfinitesimalCharacter casimirAction HAction EAction FAction
  rw [trivial_toEnd, trivial_toEnd, trivial_toEnd]
  simp

end

end LieTheory.SL2RHarishChandra
