import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceComplexAmpleDifference
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldLineRealizationReflection
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldHomogeneityBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CountableComplexEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback

/-! # Countable Ample Difference Surjectivity -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.CountableAmpleDifferenceSurjectivity.Geometric

noncomputable section

/-! An ample line on an abelian scheme over a countable algebraically
closed characteristic-zero field realizes every homogeneous line.
Complex realization is reflected through the actual comparison scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] [Countable k]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (L N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

theorem countable_ampleDifference_realizes_homogeneous_line (hL : L.IsAmple)
    (hN : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N)) :
    ∃ a : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme,
      (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
        (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op (Over.mk (𝟙 (Spec (.of k)))))
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (N.pullback (snd (Over.mk (𝟙 (Spec (.of k)))) A.scheme).left)) := by
  obtain ⟨embedding⟩ := AbelianScheme.TateComparison.CountableComplexEmbedding.countable_field_has_complex_embedding k
  let b := Spec.map (CommRingCat.ofHom embedding)
  let p := pullback.fst A.scheme.hom b
  let : IsAffineHom b := inferInstanceAs (IsAffineHom (Spec.map (CommRingCat.ofHom embedding)))
  let : IsAffineHom p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback A.scheme.hom b).flip inferInstance
  have hLc : (L.pullback p).IsAmple := hL.pullback_of_isAffineHom p
  have hNc := FieldHomogeneityBaseChange.Geometric.homogeneousLine_baseChange A N b hN
  exact FieldLineRealizationReflection.Geometric.line_realization_of_field_extension A (hL.projectivePresentation A.scheme.hom) L N b
    (ReferenceComplexAmpleDifference.Geometric.original_ampleDifference_realizes_homogeneous_line (A.pullback b) (L.pullback p) hLc (N.pullback p) hNc)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.CountableAmpleDifferenceSurjectivity.Geometric
