/-
Copyright (c) 2026 SL2RepresentationTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SL2RepresentationTheory contributors
-/
import SL2RepresentationTheory.SL2RHarishChandra.Classification

/-! # Equivalences produced by the four seed vectors -/

namespace SL2RepresentationTheory.SL2RHarishChandra

noncomputable section

set_option maxHeartbeats 1000000

variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
variable [AddCommGroup B] [Module ℂ B]
variable [LieRingModule sl2Compact A] [LieModule ℂ sl2Compact A]
variable [LieRingModule sl2Compact B] [LieModule ℂ sl2Compact B]

theorem lieModuleHom_bijective_of_ne_zero
    [LieModule.IsIrreducible ℂ sl2Compact A]
    [LieModule.IsIrreducible ℂ sl2Compact B]
    (f : A →ₗ⁅ℂ, sl2Compact⁆ B) (hf : f ≠ 0) : Function.Bijective f := by
  have hker : f.ker = ⊥ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top f.ker with h | h
    · exact h
    · exfalso
      apply hf
      apply LieModuleHom.ext
      intro x
      have hx : x ∈ f.ker := by rw [h]; trivial
      simpa using hx
  have hrange : f.range = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top f.range with h | h
    · exfalso
      apply hf
      apply LieModuleHom.ext
      intro x
      have hx : f x ∈ f.range := ⟨x, rfl⟩
      rw [h] at hx
      simpa using hx
    · exact h
  exact ⟨f.ker_eq_bot.mp hker, f.range_eq_top.mp hrange⟩

noncomputable def lieModuleEquivOfBijective (f : A →ₗ⁅ℂ, sl2Compact⁆ B)
    (hf : Function.Bijective f) : A ≃ₗ⁅ℂ, sl2Compact⁆ B :=
  LieModuleEquiv.mk f (fun y => Classical.choose (hf.2 y))
    (fun x => hf.1 (Classical.choose_spec (hf.2 (f x))))
    (fun y => Classical.choose_spec (hf.2 y))

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
variable [LieRingModule sl2Compact M] [LieModule ℂ sl2Compact M]

def trivialSeedLinearMap (v : M) : TrivialHC →ₗ[ℂ] M where
  toFun c := c • v
  map_add' a b := add_smul a b v
  map_smul' a b := by simp [mul_smul]

theorem trivialSeed_annihilated (v : M) (hv : IsTrivialSeed M v) (X : sl2Compact) :
    ⁅X, v⁆ = 0 := by
  rcases hv with ⟨_, hvH, hvE, hvF⟩
  rw [decompose X, add_lie, add_lie, smul_lie, smul_lie, smul_lie]
  rw [(mem_KWeightSpace_iff M).mp hvH, hvE, hvF]
  simp

def trivialSeedHom (v : M) (hv : IsTrivialSeed M v) :
    TrivialHC →ₗ⁅ℂ, sl2Compact⁆ M :=
  LieModuleHom.mk (trivialSeedLinearMap M v) (by
    intro X c
    change trivialSeedLinearMap M v (trivialRepresentation X c) = ⁅X, c • v⁆
    rw [show trivialRepresentation X = 0 by
      apply LinearMap.ext
      intro z
      change trivialRepresentation X z = 0
      simp [trivialRepresentation, sl2LieHomOfOperators, operatorMapLinear]]
    simp [trivialSeedLinearMap, lie_smul, trivialSeed_annihilated M v hv X])

theorem trivialSeedHom_ne_zero (v : M) (hv : IsTrivialSeed M v) :
    trivialSeedHom M v hv ≠ 0 := by
  intro h
  have h1 := DFunLike.congr_fun h (1 : ℂ)
  change trivialSeedLinearMap M v 1 = (0 : TrivialHC →ₗ⁅ℂ, sl2Compact⁆ M) 1 at h1
  simp [trivialSeedLinearMap] at h1
  exact hv.1 h1

def positiveChain (v : M) : ℕ → M
  | 0 => v
  | j + 1 => ⁅E, positiveChain v j⁆

theorem positiveChain_weight (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsPositiveSeed M v) (j : ℕ) :
    positiveChain M v j ∈ KWeightSpace M (2 + 2 * (j : ℤ)) := by
  induction j with
  | zero => simpa [positiveChain] using hv.2.1
  | succ j ih =>
      have h := E_mem_KWeightSpace M ih
      change ⁅E, positiveChain M v j⁆ ∈
        KWeightSpace M (2 + 2 * ((j + 1 : ℕ) : ℤ))
      convert h using 1
      congr 1

@[simp] theorem positiveChain_E (v : M) (j : ℕ) :
    ⁅E, positiveChain M v j⁆ = positiveChain M v (j + 1) := by
  rfl

theorem positiveChain_F (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsPositiveSeed M v) : ∀ j : ℕ,
    match j with
    | 0 => ⁅F, positiveChain M v 0⁆ = 0
    | k + 1 => ⁅F, positiveChain M v (k + 1)⁆ =
        (-((k + 1 : ℕ) : ℂ) * ((k + 2 : ℕ) : ℂ)) • positiveChain M v k := by
  intro j
  cases j with
  | zero => simpa [positiveChain] using hv.2.2
  | succ k =>
      have hw := positiveChain_weight M hrho v hv k
      have hf := rho_F_E_formula M hrho hw
      change ⁅F, ⁅E, positiveChain M v k⁆⁆ = _
      calc
        ⁅F, ⁅E, positiveChain M v k⁆⁆ =
            (4 : ℂ)⁻¹ • ((4 : ℂ) • ⁅F, ⁅E, positiveChain M v k⁆⁆) := by
              module
        _ = (4 : ℂ)⁻¹ •
            (-(((2 + 2 * (k : ℤ) : ℤ) : ℂ) *
              (((2 + 2 * (k : ℤ) : ℤ) : ℂ) + 2)) • positiveChain M v k) := by
              rw [hf]
        _ = (-((k + 1 : ℕ) : ℂ) * ((k + 2 : ℕ) : ℂ)) •
            positiveChain M v k := by
              push_cast
              module

def positiveSeedLinearMap (v : M) : HolomorphicDiscreteHC →ₗ[ℂ] M :=
  Finsupp.linearCombination ℂ (positiveChain M v)

@[simp] theorem positiveSeedLinearMap_single (v : M) (j : ℕ) (c : ℂ) :
    positiveSeedLinearMap M v (Finsupp.single j c) = c • positiveChain M v j := by
  simp [positiveSeedLinearMap]

theorem positiveSeed_intertwines_H (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsPositiveSeed M v) :
    (positiveSeedLinearMap M v).comp positiveH =
      (LieModule.toEnd ℂ sl2Compact M H).comp (positiveSeedLinearMap M v) := by
  apply Finsupp.basisSingleOne.ext
  intro j
  rw [Finsupp.coe_basisSingleOne]
  simp [positiveH]
  rw [(mem_KWeightSpace_iff M).mp (positiveChain_weight M hrho v hv j)]
  push_cast
  module

theorem positiveSeed_intertwines_E (v : M) :
    (positiveSeedLinearMap M v).comp positiveE =
      (LieModule.toEnd ℂ sl2Compact M E).comp (positiveSeedLinearMap M v) := by
  apply Finsupp.basisSingleOne.ext
  intro j
  rw [Finsupp.coe_basisSingleOne]
  simp [positiveE, positiveSeedLinearMap]

theorem positiveSeed_intertwines_F (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsPositiveSeed M v) :
    (positiveSeedLinearMap M v).comp positiveF =
      (LieModule.toEnd ℂ sl2Compact M F).comp (positiveSeedLinearMap M v) := by
  apply Finsupp.basisSingleOne.ext
  intro j
  rw [Finsupp.coe_basisSingleOne]
  cases j with
  | zero =>
      simp [positiveF, positiveFImage, positiveSeedLinearMap,
        positiveChain]
      exact (positiveChain_F M hrho v hv 0).symm
  | succ j =>
      simp [positiveF, positiveFImage, positiveSeedLinearMap]
      convert (positiveChain_F M hrho v hv (j + 1)).symm using 1 <;> push_cast <;> ring

def positiveSeedHom (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsPositiveSeed M v) :
    HolomorphicDiscreteHC →ₗ⁅ℂ, sl2Compact⁆ M :=
  LieModuleHom.mk (positiveSeedLinearMap M v) (by
    intro X m
    change positiveSeedLinearMap M v (positiveRepresentation X m) =
      (LieModule.toEnd ℂ sl2Compact M X) (positiveSeedLinearMap M v m)
    have hH := LinearMap.congr_fun (positiveSeed_intertwines_H M hrho v hv) m
    have hE := LinearMap.congr_fun (positiveSeed_intertwines_E M v) m
    have hF := LinearMap.congr_fun (positiveSeed_intertwines_F M hrho v hv) m
    change positiveSeedLinearMap M v (positiveH m) =
      (LieModule.toEnd ℂ sl2Compact M H) (positiveSeedLinearMap M v m) at hH
    change positiveSeedLinearMap M v (positiveE m) =
      (LieModule.toEnd ℂ sl2Compact M E) (positiveSeedLinearMap M v m) at hE
    change positiveSeedLinearMap M v (positiveF m) =
      (LieModule.toEnd ℂ sl2Compact M F) (positiveSeedLinearMap M v m) at hF
    have repH : positiveRepresentation H = positiveH := by
      apply LinearMap.ext; intro z
      simp [positiveRepresentation, sl2LieHomOfOperators, operatorMapLinear]
    have repE : positiveRepresentation E = positiveE := by
      apply LinearMap.ext; intro z
      simp [positiveRepresentation, sl2LieHomOfOperators, operatorMapLinear]
    have repF : positiveRepresentation F = positiveF := by
      apply LinearMap.ext; intro z
      simp [positiveRepresentation, sl2LieHomOfOperators, operatorMapLinear]
    rw [decompose X]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    rw [repH, repE, repF]
    change _ =
      X.1 0 0 • (LieModule.toEnd ℂ sl2Compact M H) (positiveSeedLinearMap M v m) +
      X.1 0 1 • (LieModule.toEnd ℂ sl2Compact M E) (positiveSeedLinearMap M v m) +
      X.1 1 0 • (LieModule.toEnd ℂ sl2Compact M F) (positiveSeedLinearMap M v m)
    rw [hH, hE, hF])

theorem positiveSeedHom_ne_zero (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsPositiveSeed M v) : positiveSeedHom M hrho v hv ≠ 0 := by
  intro h
  have h0 := DFunLike.congr_fun h (Finsupp.single 0 1)
  change positiveSeedLinearMap M v (Finsupp.single 0 1) =
    (0 : HolomorphicDiscreteHC →ₗ⁅ℂ, sl2Compact⁆ M) (Finsupp.single 0 1) at h0
  simp [positiveSeedLinearMap, positiveChain] at h0
  exact hv.1 h0

def trivialEquivOfSeed [LieModule.IsIrreducible ℂ sl2Compact M]
    (v : M) (hv : IsTrivialSeed M v) : TrivialHC ≃ₗ⁅ℂ, sl2Compact⁆ M :=
  lieModuleEquivOfBijective (trivialSeedHom M v hv)
    (lieModuleHom_bijective_of_ne_zero (trivialSeedHom M v hv)
      (trivialSeedHom_ne_zero M v hv))

def positiveEquivOfSeed [LieModule.IsIrreducible ℂ sl2Compact M]
    (hrho : HasRhoInfinitesimalCharacter M) (v : M) (hv : IsPositiveSeed M v) :
    HolomorphicDiscreteHC ≃ₗ⁅ℂ, sl2Compact⁆ M :=
  lieModuleEquivOfBijective (positiveSeedHom M hrho v hv)
    (lieModuleHom_bijective_of_ne_zero (positiveSeedHom M hrho v hv)
      (positiveSeedHom_ne_zero M hrho v hv))

def negativeChain (v : M) : ℕ → M
  | 0 => v
  | j + 1 => ⁅F, negativeChain v j⁆

theorem negativeChain_weight (v : M) (hv : IsNegativeSeed M v) (j : ℕ) :
    negativeChain M v j ∈ KWeightSpace M (-2 - 2 * (j : ℤ)) := by
  induction j with
  | zero => simpa [negativeChain] using hv.2.1
  | succ j ih =>
      have h := F_mem_KWeightSpace M ih
      change ⁅F, negativeChain M v j⁆ ∈
        KWeightSpace M (-2 - 2 * ((j + 1 : ℕ) : ℤ))
      convert h using 1
      congr 1
      push_cast
      ring

theorem negativeChain_E (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsNegativeSeed M v) : ∀ j : ℕ,
    match j with
    | 0 => ⁅E, negativeChain M v 0⁆ = 0
    | k + 1 => ⁅E, negativeChain M v (k + 1)⁆ =
        (-((k + 1 : ℕ) : ℂ) * ((k + 2 : ℕ) : ℂ)) • negativeChain M v k := by
  intro j
  cases j with
  | zero => simpa [negativeChain] using hv.2.2
  | succ k =>
      have hw := negativeChain_weight M v hv k
      have hf := rho_E_F_formula M hrho hw
      change ⁅E, ⁅F, negativeChain M v k⁆⁆ = _
      calc
        ⁅E, ⁅F, negativeChain M v k⁆⁆ =
            (4 : ℂ)⁻¹ • ((4 : ℂ) • ⁅E, ⁅F, negativeChain M v k⁆⁆) := by module
        _ = (4 : ℂ)⁻¹ •
            (-(((-2 - 2 * (k : ℤ) : ℤ) : ℂ) *
              (((-2 - 2 * (k : ℤ) : ℤ) : ℂ) - 2)) • negativeChain M v k) := by
              rw [hf]
        _ = (-((k + 1 : ℕ) : ℂ) * ((k + 2 : ℕ) : ℂ)) •
            negativeChain M v k := by
              push_cast
              module

def negativeSeedLinearMap (v : M) : AntiholomorphicDiscreteHC →ₗ[ℂ] M :=
  Finsupp.linearCombination ℂ (fun j : NegativeIndex => negativeChain M v j.down)

theorem negativeSeed_intertwines_H (v : M) (hv : IsNegativeSeed M v) :
    (negativeSeedLinearMap M v).comp negativeH =
      (LieModule.toEnd ℂ sl2Compact M H).comp (negativeSeedLinearMap M v) := by
  apply Finsupp.basisSingleOne.ext
  rintro ⟨j⟩
  rw [Finsupp.coe_basisSingleOne]
  simp [negativeH, negativeSeedLinearMap]
  rw [(mem_KWeightSpace_iff M).mp (negativeChain_weight M v hv j)]
  push_cast
  module

theorem negativeSeed_intertwines_F (v : M) :
    (negativeSeedLinearMap M v).comp negativeF =
      (LieModule.toEnd ℂ sl2Compact M F).comp (negativeSeedLinearMap M v) := by
  apply Finsupp.basisSingleOne.ext
  rintro ⟨j⟩
  rw [Finsupp.coe_basisSingleOne]
  simp [negativeF, negativeSeedLinearMap, negativeChain]

theorem negativeSeed_intertwines_E (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsNegativeSeed M v) :
    (negativeSeedLinearMap M v).comp negativeE =
      (LieModule.toEnd ℂ sl2Compact M E).comp (negativeSeedLinearMap M v) := by
  apply Finsupp.basisSingleOne.ext
  rintro ⟨j⟩
  rw [Finsupp.coe_basisSingleOne]
  cases j with
  | zero =>
      simp [negativeE, negativeEImage, negativeSeedLinearMap, negativeChain]
      exact (negativeChain_E M hrho v hv 0).symm
  | succ j =>
      simp [negativeE, negativeEImage, negativeSeedLinearMap]
      convert (negativeChain_E M hrho v hv (j + 1)).symm using 1 <;> push_cast <;> ring

def negativeSeedHom (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsNegativeSeed M v) :
    AntiholomorphicDiscreteHC →ₗ⁅ℂ, sl2Compact⁆ M :=
  LieModuleHom.mk (negativeSeedLinearMap M v) (by
    intro X m
    change negativeSeedLinearMap M v (negativeRepresentation X m) =
      (LieModule.toEnd ℂ sl2Compact M X) (negativeSeedLinearMap M v m)
    have hH := LinearMap.congr_fun (negativeSeed_intertwines_H M v hv) m
    have hE := LinearMap.congr_fun (negativeSeed_intertwines_E M hrho v hv) m
    have hF := LinearMap.congr_fun (negativeSeed_intertwines_F M v) m
    change negativeSeedLinearMap M v (negativeH m) =
      (LieModule.toEnd ℂ sl2Compact M H) (negativeSeedLinearMap M v m) at hH
    change negativeSeedLinearMap M v (negativeE m) =
      (LieModule.toEnd ℂ sl2Compact M E) (negativeSeedLinearMap M v m) at hE
    change negativeSeedLinearMap M v (negativeF m) =
      (LieModule.toEnd ℂ sl2Compact M F) (negativeSeedLinearMap M v m) at hF
    have repH : negativeRepresentation H = negativeH := by
      apply LinearMap.ext; intro z
      simp [negativeRepresentation, sl2LieHomOfOperators, operatorMapLinear]
    have repE : negativeRepresentation E = negativeE := by
      apply LinearMap.ext; intro z
      simp [negativeRepresentation, sl2LieHomOfOperators, operatorMapLinear]
    have repF : negativeRepresentation F = negativeF := by
      apply LinearMap.ext; intro z
      simp [negativeRepresentation, sl2LieHomOfOperators, operatorMapLinear]
    rw [decompose X]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    rw [repH, repE, repF]
    change _ =
      X.1 0 0 • (LieModule.toEnd ℂ sl2Compact M H) (negativeSeedLinearMap M v m) +
      X.1 0 1 • (LieModule.toEnd ℂ sl2Compact M E) (negativeSeedLinearMap M v m) +
      X.1 1 0 • (LieModule.toEnd ℂ sl2Compact M F) (negativeSeedLinearMap M v m)
    rw [hH, hE, hF])

theorem negativeSeedHom_ne_zero (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsNegativeSeed M v) : negativeSeedHom M hrho v hv ≠ 0 := by
  intro h
  let e0 : AntiholomorphicDiscreteHC :=
    Finsupp.single (ULift.up (0 : ℕ) : NegativeIndex) (1 : ℂ)
  have h0 := DFunLike.congr_fun h e0
  change negativeSeedLinearMap M v e0 =
    (0 : AntiholomorphicDiscreteHC →ₗ⁅ℂ, sl2Compact⁆ M)
      e0 at h0
  simp [e0, negativeSeedLinearMap, negativeChain] at h0
  exact hv.1 h0

def negativeEquivOfSeed [LieModule.IsIrreducible ℂ sl2Compact M]
    (hrho : HasRhoInfinitesimalCharacter M) (v : M) (hv : IsNegativeSeed M v) :
    AntiholomorphicDiscreteHC ≃ₗ⁅ℂ, sl2Compact⁆ M :=
  lieModuleEquivOfBijective (negativeSeedHom M hrho v hv)
    (lieModuleHom_bijective_of_ne_zero (negativeSeedHom M hrho v hv)
      (negativeSeedHom_ne_zero M hrho v hv))

def oddCoefficient (j : ℤ) : ℂ := (1 - 4 * (j : ℂ) ^ 2) / 4

theorem oddCoefficient_ne_zero (j : ℤ) : oddCoefficient j ≠ 0 := by
  exact oddFCoefficient_ne_zero j

private theorem rho_EF_eq_oddCoefficient (hrho : HasRhoInfinitesimalCharacter M)
    (j : ℤ) {w : M} (hw : w ∈ KWeightSpace M (2 * j + 1)) :
    ⁅E, ⁅F, w⁆⁆ = oddCoefficient j • w := by
  have h := rho_E_F_formula M hrho hw
  calc
    ⁅E, ⁅F, w⁆⁆ = (4 : ℂ)⁻¹ • ((4 : ℂ) • ⁅E, ⁅F, w⁆⁆) := by module
    _ = (4 : ℂ)⁻¹ •
        (-(((2 * j + 1 : ℤ) : ℂ) * (((2 * j + 1 : ℤ) : ℂ) - 2)) • w) := by
          rw [h]
    _ = oddCoefficient j • w := by
      push_cast
      dsimp [oddCoefficient]
      module

private theorem rho_FE_eq_nextOddCoefficient (hrho : HasRhoInfinitesimalCharacter M)
    (j : ℤ) {w : M} (hw : w ∈ KWeightSpace M (2 * j + 1)) :
    ⁅F, ⁅E, w⁆⁆ = oddCoefficient (j + 1) • w := by
  have h := rho_F_E_formula M hrho hw
  calc
    ⁅F, ⁅E, w⁆⁆ = (4 : ℂ)⁻¹ • ((4 : ℂ) • ⁅F, ⁅E, w⁆⁆) := by module
    _ = (4 : ℂ)⁻¹ •
        (-(((2 * j + 1 : ℤ) : ℂ) * (((2 * j + 1 : ℤ) : ℂ) + 2)) • w) := by
          rw [h]
    _ = oddCoefficient (j + 1) • w := by
      push_cast
      dsimp [oddCoefficient]
      module

def oddUp (v : M) : ℕ → M
  | 0 => v
  | n + 1 => ⁅E, oddUp v n⁆

def oddDown (v : M) : ℕ → M
  | 0 => v
  | n + 1 => (oddCoefficient (-(n : ℤ)))⁻¹ • ⁅F, oddDown v n⁆

def oddChain (v : M) : ℤ → M
  | Int.ofNat n => oddUp M v n
  | Int.negSucc n => oddDown M v (n + 1)

theorem oddUp_weight (v : M) (hv : IsOddSeed M v) (n : ℕ) :
    oddUp M v n ∈ KWeightSpace M (2 * (n : ℤ) + 1) := by
  induction n with
  | zero => simpa [oddUp] using hv.2
  | succ n ih =>
      have h := E_mem_KWeightSpace M ih
      change ⁅E, oddUp M v n⁆ ∈ KWeightSpace M (2 * ((n + 1 : ℕ) : ℤ) + 1)
      convert h using 1
      congr 1

theorem oddDown_weight (v : M) (hv : IsOddSeed M v) (n : ℕ) :
    oddDown M v n ∈ KWeightSpace M (2 * (-(n : ℤ)) + 1) := by
  induction n with
  | zero => simpa [oddDown] using hv.2
  | succ n ih =>
      have hF : ⁅F, oddDown M v n⁆ ∈
          KWeightSpace M ((2 * (-(n : ℤ)) + 1) - 2) :=
        F_mem_KWeightSpace M ih
      have h := (KWeightSpace M ((2 * (-(n : ℤ)) + 1) - 2)).smul_mem
        (oddCoefficient (-(n : ℤ)))⁻¹ hF
      change (oddCoefficient (-(n : ℤ)))⁻¹ • ⁅F, oddDown M v n⁆ ∈
        KWeightSpace M (2 * (-((n + 1 : ℕ) : ℤ)) + 1)
      convert h using 1
      congr 1
      push_cast
      ring

private theorem oddUp_F (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsOddSeed M v) : ∀ n : ℕ,
    ⁅F, oddUp M v n⁆ = oddCoefficient (n : ℤ) •
      oddChain M v ((n : ℤ) - 1) := by
  intro n
  cases n with
  | zero =>
      change ⁅F, v⁆ = oddCoefficient 0 •
        ((oddCoefficient 0)⁻¹ • ⁅F, v⁆)
      rw [smul_smul, mul_inv_cancel₀ (oddCoefficient_ne_zero 0), one_smul]
  | succ n =>
      change ⁅F, ⁅E, oddUp M v n⁆⁆ = _
      rw [rho_FE_eq_nextOddCoefficient M hrho (n : ℤ) (oddUp_weight M v hv n)]
      congr 1
      simp [oddChain, oddUp]

private theorem oddDown_E (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsOddSeed M v) : ∀ n : ℕ,
    ⁅E, oddDown M v (n + 1)⁆ = oddDown M v n := by
  intro n
  rw [oddDown, lie_smul]
  rw [rho_EF_eq_oddCoefficient M hrho (-(n : ℤ)) (oddDown_weight M v hv n)]
  rw [smul_smul, inv_mul_cancel₀ (oddCoefficient_ne_zero (-(n : ℤ))), one_smul]

theorem oddChain_weight (v : M) (hv : IsOddSeed M v) (j : ℤ) :
    oddChain M v j ∈ KWeightSpace M (2 * j + 1) := by
  cases j with
  | ofNat n => exact oddUp_weight M v hv n
  | negSucc n =>
      simpa [oddChain, Int.negSucc_eq] using oddDown_weight M v hv (n + 1)

theorem oddChain_E (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsOddSeed M v) (j : ℤ) :
    ⁅E, oddChain M v j⁆ = oddChain M v (j + 1) := by
  cases j with
  | ofNat n => rfl
  | negSucc n =>
      cases n with
      | zero =>
          change ⁅E, oddDown M v 1⁆ = oddChain M v (Int.negSucc 0 + 1)
          rw [show Int.negSucc 0 + 1 = 0 by omega]
          exact oddDown_E M hrho v hv 0
      | succ n =>
          change ⁅E, oddDown M v (n + 2)⁆ = oddChain M v (Int.negSucc (n + 1) + 1)
          rw [show Int.negSucc (n + 1) + 1 = Int.negSucc n by omega]
          exact oddDown_E M hrho v hv (n + 1)

theorem oddChain_F (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsOddSeed M v) (j : ℤ) :
    ⁅F, oddChain M v j⁆ = oddCoefficient j • oddChain M v (j - 1) := by
  cases j with
  | ofNat n => exact oddUp_F M hrho v hv n
  | negSucc n =>
      change ⁅F, oddDown M v (n + 1)⁆ =
        oddCoefficient (Int.negSucc n) • oddChain M v (Int.negSucc n - 1)
      rw [show Int.negSucc n = -(n : ℤ) - 1 by omega,
        show (-(n : ℤ) - 1) - 1 = Int.negSucc (n + 1) by omega]
      change ⁅F, oddDown M v (n + 1)⁆ =
        oddCoefficient (-(n : ℤ) - 1) • oddDown M v ((n + 1) + 1)
      have hdef := congrArg (fun w : M => oddCoefficient (-(n : ℤ) - 1) • w)
        (show oddDown M v (n + 2) =
          (oddCoefficient (-(n : ℤ) - 1))⁻¹ • ⁅F, oddDown M v (n + 1)⁆ by
            rw [oddDown]
            congr 2 <;> push_cast <;> ring)
      have hc := oddCoefficient_ne_zero (-(n : ℤ) - 1)
      simpa [oddChain, Int.negSucc_eq, smul_smul, hc] using hdef.symm

def oddSeedLinearMap (v : M) : OddPrincipalHC →ₗ[ℂ] M :=
  Finsupp.linearCombination ℂ (oddChain M v)

theorem oddSeed_intertwines_H (v : M) (hv : IsOddSeed M v) :
    (oddSeedLinearMap M v).comp oddH =
      (LieModule.toEnd ℂ sl2Compact M H).comp (oddSeedLinearMap M v) := by
  apply Finsupp.basisSingleOne.ext
  intro j
  rw [Finsupp.coe_basisSingleOne]
  simp [oddH, oddSeedLinearMap]
  rw [(mem_KWeightSpace_iff M).mp (oddChain_weight M v hv j)]
  push_cast
  module

theorem oddSeed_intertwines_E (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsOddSeed M v) :
    (oddSeedLinearMap M v).comp oddE =
      (LieModule.toEnd ℂ sl2Compact M E).comp (oddSeedLinearMap M v) := by
  apply Finsupp.basisSingleOne.ext
  intro j
  rw [Finsupp.coe_basisSingleOne]
  simp [oddE, oddSeedLinearMap]
  exact (oddChain_E M hrho v hv j).symm

theorem oddSeed_intertwines_F (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsOddSeed M v) :
    (oddSeedLinearMap M v).comp oddF =
      (LieModule.toEnd ℂ sl2Compact M F).comp (oddSeedLinearMap M v) := by
  apply Finsupp.basisSingleOne.ext
  intro j
  rw [Finsupp.coe_basisSingleOne]
  simp [oddF, oddSeedLinearMap]
  change oddCoefficient j • oddChain M v (j - 1) = ⁅F, oddChain M v j⁆
  exact (oddChain_F M hrho v hv j).symm

def oddSeedHom (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsOddSeed M v) : OddPrincipalHC →ₗ⁅ℂ, sl2Compact⁆ M :=
  LieModuleHom.mk (oddSeedLinearMap M v) (by
    intro X m
    change oddSeedLinearMap M v (oddRepresentation X m) =
      (LieModule.toEnd ℂ sl2Compact M X) (oddSeedLinearMap M v m)
    have hH := LinearMap.congr_fun (oddSeed_intertwines_H M v hv) m
    have hE := LinearMap.congr_fun (oddSeed_intertwines_E M hrho v hv) m
    have hF := LinearMap.congr_fun (oddSeed_intertwines_F M hrho v hv) m
    change oddSeedLinearMap M v (oddH m) =
      (LieModule.toEnd ℂ sl2Compact M H) (oddSeedLinearMap M v m) at hH
    change oddSeedLinearMap M v (oddE m) =
      (LieModule.toEnd ℂ sl2Compact M E) (oddSeedLinearMap M v m) at hE
    change oddSeedLinearMap M v (oddF m) =
      (LieModule.toEnd ℂ sl2Compact M F) (oddSeedLinearMap M v m) at hF
    have repH : oddRepresentation H = oddH := by
      apply LinearMap.ext; intro z
      simp [oddRepresentation, sl2LieHomOfOperators, operatorMapLinear]
    have repE : oddRepresentation E = oddE := by
      apply LinearMap.ext; intro z
      simp [oddRepresentation, sl2LieHomOfOperators, operatorMapLinear]
    have repF : oddRepresentation F = oddF := by
      apply LinearMap.ext; intro z
      simp [oddRepresentation, sl2LieHomOfOperators, operatorMapLinear]
    rw [decompose X]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    rw [repH, repE, repF]
    change _ =
      X.1 0 0 • (LieModule.toEnd ℂ sl2Compact M H) (oddSeedLinearMap M v m) +
      X.1 0 1 • (LieModule.toEnd ℂ sl2Compact M E) (oddSeedLinearMap M v m) +
      X.1 1 0 • (LieModule.toEnd ℂ sl2Compact M F) (oddSeedLinearMap M v m)
    rw [hH, hE, hF])

theorem oddSeedHom_ne_zero (hrho : HasRhoInfinitesimalCharacter M)
    (v : M) (hv : IsOddSeed M v) : oddSeedHom M hrho v hv ≠ 0 := by
  intro h
  let e0 : OddPrincipalHC := Finsupp.single (0 : ℤ) (1 : ℂ)
  have h0 := DFunLike.congr_fun h e0
  change oddSeedLinearMap M v e0 =
    (0 : OddPrincipalHC →ₗ⁅ℂ, sl2Compact⁆ M) e0 at h0
  simp [e0, oddSeedLinearMap, oddChain, oddUp] at h0
  exact hv.1 h0

def oddEquivOfSeed [LieModule.IsIrreducible ℂ sl2Compact M]
    (hrho : HasRhoInfinitesimalCharacter M) (v : M) (hv : IsOddSeed M v) :
    OddPrincipalHC ≃ₗ⁅ℂ, sl2Compact⁆ M :=
  lieModuleEquivOfBijective (oddSeedHom M hrho v hv)
    (lieModuleHom_bijective_of_ne_zero (oddSeedHom M hrho v hv)
      (oddSeedHom_ne_zero M hrho v hv))

end


end SL2RepresentationTheory.SL2RHarishChandra
