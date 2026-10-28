import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.SingleDegreeGeneration

/-! # Degree Relation Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.DegreeRelationExtension

noncomputable section

/-! Extending one homogeneous relation submodule by repeated variable multiplication, with exact recovery of its generated ideal. -/

universe u v

variable {R : Type u} [CommRing R] {σ : Type v} (N : ℕ)
variable (K : Submodule R (MvPolynomial.homogeneousSubmodule σ R N))

def singleDegreePiece : ∀ d : ℕ, Submodule R (MvPolynomial.homogeneousSubmodule σ R d)
  | 0 => if h : 0 = N then h ▸ K else ⊥
  | d + 1 => if h : d + 1 = N then h ▸ K else
      if N < d + 1 then ⨆ i : σ, (singleDegreePiece d).map (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i) else ⊥

theorem singleDegreePiece_at : DegreeRelationExtension.singleDegreePiece N K N = K := by
  cases N with
  | zero => simp [DegreeRelationExtension.singleDegreePiece]
  | succ N => simp [DegreeRelationExtension.singleDegreePiece]

theorem singleDegreePiece_below (d : ℕ) (hd : d < N) : DegreeRelationExtension.singleDegreePiece N K d = ⊥ := by
  cases d with
  | zero => simp only [DegreeRelationExtension.singleDegreePiece, dite_eq_right (show ¬0 = N by omega)]
  | succ d =>
    simp only [DegreeRelationExtension.singleDegreePiece, dite_eq_right (show ¬d + 1 = N by omega),
      ite_eq_right (show ¬N < d + 1 by omega)]

theorem singleDegreePiece_succ (d : ℕ) (hd : N ≤ d) :
    DegreeRelationExtension.singleDegreePiece N K (d + 1) =
      ⨆ i : σ, (DegreeRelationExtension.singleDegreePiece N K d).map (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i) := by
  simp only [DegreeRelationExtension.singleDegreePiece, dite_eq_right (show ¬d + 1 = N by omega),
    ite_eq_left (show N < d + 1 by omega)]

def singleDegreeRelations : GradedIdealReconstruction.GradedIdealRelations R σ where
  piece := DegreeRelationExtension.singleDegreePiece N K
  variable_mul d i := by
    by_cases hd : N ≤ d
    · rw [singleDegreePiece_succ N K d hd]
      exact Submodule.map_le_iff_le_comap.mp (le_iSup
        (fun j : σ => (DegreeRelationExtension.singleDegreePiece N K d).map (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d j)) i)
    · rw [singleDegreePiece_below N K d (by omega)]
      exact bot_le

theorem singleDegreeRelations_ideal :
    (singleDegreeRelations N K).toIdeal = Ideal.span
      (K.map (MvPolynomial.homogeneousSubmodule σ R N).subtype : Set (MvPolynomial σ R)) := by
  rw [← (singleDegreeRelations N K).lowDegreeIdeal_eq N (singleDegreePiece_succ N K)]
  change Ideal.span ((singleDegreeRelations N K).lowDegreeRelations N : Set (MvPolynomial σ R)) = _
  rw [(singleDegreeRelations N K).lowDegreeRelations_eq_last N (singleDegreePiece_below N K)]
  change Ideal.span ((DegreeRelationExtension.singleDegreePiece N K N).map
    (MvPolynomial.homogeneousSubmodule σ R N).subtype : Set (MvPolynomial σ R)) = _
  rw [singleDegreePiece_at]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.DegreeRelationExtension
