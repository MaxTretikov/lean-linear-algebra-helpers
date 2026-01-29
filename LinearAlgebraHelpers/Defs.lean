/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Common Linear Algebra Definitions

Shared definitions used across linear programming and polyhedral geometry libraries.

THIS SUCKS TOTAL ASS
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

/-- The standard Euclidean space ℝ^n. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Matrix type over reals. -/
abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- The nonnegative orthant: all vectors with nonnegative coordinates. -/
def nonnegOrthant (n : ℕ) : Set (Vec n) := { x | ∀ i, 0 ≤ x i }

/-! ## Matrix/Linear-Map Utilities -/

lemma toEuclideanLin_mulVec {m p : ℕ} (B : Mat m p) (y : Vec p) :
    Matrix.toEuclideanLin B y = WithLp.toLp _ (B.mulVec y.ofLp) := by
  simpa using (Matrix.toEuclideanLin_apply (M := B) (v := y))

lemma toMatrix_mulVec_basisFun {m : ℕ} (f : Vec m →ₗ[ℝ] Vec m) (x : Vec m) :
    (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin m) ℝ).toBasis f).mulVec x = f x := by
  classical
  ext i
  have h :=
    (LinearMap.toMatrix_mulVec_repr
      (v₁ := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis)
      (v₂ := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis) f x)
  have h' := congrArg (fun v => v i) h
  simpa [Matrix.mulVec, EuclideanSpace.basisFun_repr, PiLp.toLp_apply] using h'

end
