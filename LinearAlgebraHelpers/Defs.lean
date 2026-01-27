/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Common Linear Algebra Definitions

Shared definitions used across linear programming and polyhedral geometry libraries.

THIS SUCKS TOTAL ASS
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic

noncomputable section

/-- The standard Euclidean space ℝ^n. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Matrix type over reals. -/
abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- The nonnegative orthant: all vectors with nonnegative coordinates. -/
def nonnegOrthant (n : ℕ) : Set (Vec n) := { x | ∀ i, 0 ≤ x i }

end
