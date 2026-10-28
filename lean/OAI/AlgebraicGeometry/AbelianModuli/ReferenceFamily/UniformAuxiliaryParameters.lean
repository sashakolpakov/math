import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.GraphHilbertRankRealization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AuxiliaryLevelFrameBounds
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.GraphTorsionSectionDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GraphIntersectionData

/-! # Uniform Auxiliary Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniformAuxiliaryParameters

noncomputable section

/-! Explicit parameters for the single auxiliary-level pure moduli
space used in ReferenceFamily. The relation degree meets both Hilbert bounds, and
the auxiliary level meets both the frame and torsion-detection bounds.
Its Hilbert rank profile is realized by the actual reference PEL fiber. -/

def uniformRelationDegree (g : ℕ) (δ : Fin g → ℕ) : ℕ :=
  max 1 (max
    (HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1)
      (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ))
    (HilbertScheme.Presentations.Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{0} (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1)
      (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ)))

theorem uniformRelationDegree_pos (g : ℕ) (δ : Fin g → ℕ) :
    0 < uniformRelationDegree g δ :=
  Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_left _ _)

theorem uniformHilbertFamilyDegree_le_relationDegree (g : ℕ) (δ : Fin g → ℕ) :
    HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1)
      (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) ≤ uniformRelationDegree g δ :=
  (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem hilbertParameterDegree_le_relationDegree (g : ℕ) (δ : Fin g → ℕ) :
    HilbertScheme.Presentations.Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{0} (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1)
      (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) ≤ uniformRelationDegree g δ :=
  (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

def uniformAuxiliaryLevel (g : ℕ) (δ : Fin g → ℕ) : ℕ :=
  HilbertConstruction.AuxiliaryLevelFrameBounds.frameAuxiliaryLevel 3 (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ + 1)
    (max (HilbertConstruction.Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ)
      (HilbertConstruction.Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ (uniformRelationDegree g δ)))

theorem uniformAuxiliaryLevel_ne_zero (g : ℕ) (δ : Fin g → ℕ) :
    uniformAuxiliaryLevel g δ ≠ 0 :=
  pow_ne_zero _ (by decide : (3 : ℕ) ≠ 0)

theorem uniformAuxiliaryLevel_three_le (g : ℕ) (δ : Fin g → ℕ) :
    3 ≤ uniformAuxiliaryLevel g δ := by
  unfold uniformAuxiliaryLevel HilbertConstruction.AuxiliaryLevelFrameBounds.frameAuxiliaryLevel
  rw [pow_succ]
  simpa only [Nat.one_mul] using
    Nat.mul_le_mul_right 3 (Nat.succ_le_of_lt (pow_pos (by decide : (0 : ℕ) < 3) _))

theorem uniformAuxiliaryLevel_frame_bound (g : ℕ) (δ : Fin g → ℕ) :
    HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * HilbertConstruction.Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ <
      uniformAuxiliaryLevel g δ ^ 2 := by
  exact (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_max_left _ _)).trans_lt
    (HilbertConstruction.AuxiliaryLevelFrameBounds.frameAuxiliaryLevel_square_gt 3 _ _ (by decide))

theorem uniformAuxiliaryLevel_detection_bound (g : ℕ) (δ : Fin g → ℕ) :
    HilbertConstruction.Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ (uniformRelationDegree g δ) <
      uniformAuxiliaryLevel g δ ^ 2 := by
  let B := max (HilbertConstruction.Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ)
    (HilbertConstruction.Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ (uniformRelationDegree g δ))
  have hB : HilbertConstruction.Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ (uniformRelationDegree g δ) ≤ B :=
    Nat.le_max_right _ _
  have hr : B ≤ (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ + 1) * B := by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right B (Nat.succ_le_succ (Nat.zero_le _))
  exact (hB.trans hr).trans_lt (HilbertConstruction.AuxiliaryLevelFrameBounds.frameAuxiliaryLevel_square_gt 3 _ B (by decide))

theorem uniformAuxiliaryParameters_rankProfile
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) (hs : 0 < s) :
    HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0}
      (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank (3 * s) P.polarizationType - 1)
      (uniformRelationDegree (3 * s) P.polarizationType)
      (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0}
        (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank (3 * s) P.polarizationType - 1)
        (uniformRelationDegree (3 * s) P.polarizationType)
        (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial (3 * s) P.polarizationType))
      (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial (3 * s) P.polarizationType) :=
  Reference.GraphHilbertRankRealization.referenceUniformGraphHilbert_rankProfile P hP hs _
    (hilbertParameterDegree_le_relationDegree _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniformAuxiliaryParameters
