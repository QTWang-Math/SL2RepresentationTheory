/-
Copyright (c) 2026 SL2RepresentationTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SL2RepresentationTheory contributors
-/
import Mathlib
import SL2RepresentationTheory.Basic

/-!
# SL2RepresentationTheory smoke tests

These examples check basic algebra, mathlib's group/ring hierarchy, and the
standard commutator Lie algebra on square matrices.
-/

open SL2RepresentationTheory

attribute [local instance 100] LieRing.ofAssociativeRing

-- Basic algebra and a theorem discharged by an existing mathlib tactic.
example (x y : ℚ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

-- A group theorem using the generic group API from mathlib.
example {G : Type*} [Group G] (g : G) : g⁻¹ * g = 1 := by
  exact inv_mul_cancel g

-- A ring theorem using an existing mathlib lemma.
example {R : Type*} [Ring R] (a b : R) : a * (b + 1) = a * b + a := by
  simpa using mul_add a b 1

-- A simple abelian Lie algebra over an arbitrary field.
example (K : Type*) [Field K] : LieAlgebra K (AbelianLieAlgebra K) :=
  inferInstance

-- The 2-by-2 matrix Lie algebra over the rationals is available in mathlib.
example : LieAlgebra ℚ (gl ℚ 2) :=
  inferInstance

-- Its Lie bracket is the matrix commutator.
example (A B : gl ℚ 2) : ⁅A, B⁆ = A * B - B * A := by
  rfl

-- Antisymmetry is one of the standard Lie ring lemmas.
example (A B : gl ℚ 2) : ⁅A, B⁆ = -⁅B, A⁆ := by
  exact (lie_skew A B).symm

def main : IO Unit :=
  IO.println "SL2RepresentationTheory: Lean 4 and mathlib are configured successfully."
