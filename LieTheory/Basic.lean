/-
Copyright (c) 2026 LieTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LieTheory contributors
-/
import Mathlib

/-!
# LieTheory.Basic

Small reusable definitions with which to start the Lie theory development.
-/

namespace LieTheory

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A field viewed as an abelian Lie algebra over itself.  Its bracket is the
commutator `x * y - y * x`, which vanishes because the field is commutative. -/
abbrev AbelianLieAlgebra (K : Type*) [Field K] := K

/-- The general linear Lie algebra of `n x n` matrices over a field. -/
abbrev gl (K : Type*) [Field K] (n : ℕ) := Matrix (Fin n) (Fin n) K

example (K : Type*) [Field K] : LieAlgebra K (AbelianLieAlgebra K) :=
  inferInstance

example (K : Type*) [Field K] (n : ℕ) : LieAlgebra K (gl K n) :=
  inferInstance

end LieTheory
