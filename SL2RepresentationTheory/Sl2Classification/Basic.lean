/-
Copyright (c) 2026 SL2RepresentationTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SL2RepresentationTheory contributors
-/
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Basic definitions for the finite-dimensional `sl₂` classification

Mathlib already proves the primitive-vector existence theorem and all three
`sl₂`-string formulas. This development builds the highest-weight basis and
classification on top of those results.
-/

namespace SL2RepresentationTheory.Sl2Classification

open LieModule

universe u v w

variable {K : Type u} {L : Type v}
variable [Field K] [LieRing L] [LieAlgebra K L]
variable {h e f : L}

/-- The explicit hypothesis that the three members of an `sl₂` triple generate
the ambient Lie algebra. -/
def IsGenerating (t : IsSl2Triple h e f) : Prop :=
  t.toLieSubalgebra K = ⊤

end SL2RepresentationTheory.Sl2Classification
