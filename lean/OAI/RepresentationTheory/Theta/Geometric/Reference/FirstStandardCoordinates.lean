import OAI.RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding
import OAI.RepresentationTheory.Theta.Geometric.Reference.EmbeddingDistinction
import OAI.RepresentationTheory.Theta.Geometric.ConstantPiCoordinates

/-! # First Standard Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference.FirstStandardCoordinates

noncomputable section

/-! The original reference first embedding inclusion is the literal
single distinguished block in standard complexified field coordinates. -/

set_option backward.isDefEq.respectTransparency false
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

theorem referenceFirstComplexInclusion_eq_standard (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    FirstEmbedding.referenceFirstComplexInclusion P hP v =
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E).symm (Pi.single (P.embeddings P.distinguished) v) := by
  apply (P.referenceComplexCoordinates hP).injective
  change P.referenceComplexCoordinates hP ((P.referenceComplexCoordinates hP).symm
    (FirstEmbedding.firstEmbeddingInclusion P.distinguished v)) = _
  rw [LinearEquiv.apply_symm_apply]
  unfold AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.referenceComplexCoordinates
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.trans_apply, ConstantPiCoordinates.linearPiCongrLeft_constant]
  change FirstEmbedding.firstEmbeddingInclusion P.distinguished v = fun i =>
    ((Pi.single (P.embeddings P.distinguished) v : (E →ₐ[ℚ] ℂ) → Geometry.ComplexBall.PrescribedSignsB.Vec) (P.embeddings i),
      (Pi.single (P.embeddings P.distinguished) v : (E →ₐ[ℚ] ℂ) → Geometry.ComplexBall.PrescribedSignsB.Vec) (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)))
  funext i
  apply Prod.ext
  · by_cases hi : i = P.distinguished
    · subst i
      simp [FirstEmbedding.firstEmbeddingInclusion]
    · have hn : P.embeddings i ≠ P.embeddings P.distinguished :=
        fun he => hi (EmbeddingDistinction.reference_embedding_injective P hP he)
      simp [FirstEmbedding.firstEmbeddingInclusion, hi, hn]
  · by_cases hi : i = P.distinguished <;>
      simp [FirstEmbedding.firstEmbeddingInclusion, hi, EmbeddingDistinction.reference_conjugate_embedding_ne P hP]

theorem referenceFirst_standardCoordinates (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E (FirstEmbedding.referenceFirstComplexInclusion P hP v) =
      Pi.single (P.embeddings P.distinguished) v := by
  rw [referenceFirstComplexInclusion_eq_standard, LinearEquiv.apply_symm_apply]

end

end OAI.RepresentationTheory.Theta.Geometric.Reference.FirstStandardCoordinates
