/-
Coordinate selection utilities.
-/

import LinearAlgebraHelpers.Defs
import Mathlib.Data.Finset.Sort

noncomputable section

namespace LinearAlgebraHelpers

variable {n : ℕ}

/-- Order-embedding of coordinates selected by a finset. -/
def coordEmb (S : Finset (Fin n)) : Fin S.card ↪ Fin n :=
  (S.orderEmbOfFin rfl).toEmbedding

/-- Project a vector to the coordinates in `S` (in increasing order). -/
def projectVec (S : Finset (Fin n)) (x : Vec n) : Vec S.card :=
  WithLp.toLp 2 (fun j => x (coordEmb S j))

/-- Expand a vector on `S` to the full space by filling missing coordinates with zero. -/
def expandVec (S : Finset (Fin n)) (x : Vec S.card) : Vec n :=
  WithLp.toLp 2 fun i =>
    if h : i ∈ S then x ((S.orderIsoOfFin rfl).symm ⟨i, h⟩) else 0

lemma coordEmb_mem (S : Finset (Fin n)) (j : Fin S.card) :
    coordEmb S j ∈ S := by
  simpa [coordEmb] using (Finset.orderEmbOfFin_mem (s := S) (h := rfl) j)

lemma project_expand (S : Finset (Fin n)) (x : Vec S.card) :
    projectVec S (expandVec S x) = x := by
  classical
  ext j
  have hj : coordEmb S j ∈ S := coordEmb_mem (S := S) j
  have hco : (S.orderIsoOfFin rfl) j = ⟨coordEmb S j, hj⟩ := by
    apply Subtype.ext
    simp [coordEmb]
  have hsymm : (S.orderIsoOfFin rfl).symm ⟨coordEmb S j, hj⟩ = j := by
    simpa [hco] using (S.orderIsoOfFin rfl).symm_apply_apply j
  simp [projectVec, expandVec, PiLp.toLp_apply, hj, hsymm]

/-- A vector is zero outside `S`. -/
def zeroOutside (S : Finset (Fin n)) (x : Vec n) : Prop :=
  ∀ i, i ∉ S → x i = 0

lemma expand_project_of_zeroOutside (S : Finset (Fin n)) (x : Vec n)
    (hx : zeroOutside S x) :
    expandVec S (projectVec S x) = x := by
  classical
  ext i
  by_cases hi : i ∈ S
  · have hcoord :
        coordEmb S ((S.orderIsoOfFin rfl).symm ⟨i, hi⟩) = i := by
        have h := (S.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩
        have h' := congrArg Subtype.val h
        have h'' := h'
        -- rewrite the LHS to an `orderEmbOfFin` expression without using simp
        rw [Finset.coe_orderIsoOfFin_apply] at h''
        dsimp [coordEmb]
        exact h''
    simp [expandVec, projectVec, PiLp.toLp_apply, hi, hcoord]
  · simp [expandVec, hi, hx i hi]

end LinearAlgebraHelpers
