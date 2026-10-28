import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeComparison
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RigidifiedConstantLine
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceBaseChangeValues
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalPointLift

/-! # Field Line Realization Reflection -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldLineRealizationReflection.Geometric

noncomputable section

/-! Realization of a field-line class by translation can be reflected
from an extension field to an algebraically closed ground field. The
witness is a rational point of the actual finite-type comparison scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {k K : Type} [Field k] [IsAlgClosed k] [Field K] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (L N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (b : Spec (.of K) ⟶ Spec (.of k))

include P in
theorem line_realization_of_field_extension
    (h : ∃ a : Over.mk (𝟙 (Spec (.of K))) ⟶ (A.pullback b).scheme,
      (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference (A.pullback b) (L.pullback (pullback.fst A.scheme.hom b))).relativeValue a =
        (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard (A.pullback b).scheme).app (.op (Over.mk (𝟙 (Spec (.of K)))))
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((N.pullback (pullback.fst A.scheme.hom b)).pullback
            (snd (Over.mk (𝟙 (Spec (.of K)))) (A.pullback b).scheme).left))) :
    ∃ a : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme,
      (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
        (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op (Over.mk (𝟙 (Spec (.of k)))))
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (N.pullback (snd (Over.mk (𝟙 (Spec (.of k)))) A.scheme).left)) := by
  let U := Over.mk (𝟙 (Spec (.of k)))
  let V := Over.mk (𝟙 (Spec (.of K)))
  let W := (Over.map b).obj V
  let t : W ⟶ U := Over.homMk b (by
    change b ≫ 𝟙 (Spec (.of k)) = 𝟙 (Spec (.of K)) ≫ b
    simp only [Category.comp_id, Category.id_comp])
  let : LocallyOfFiniteType (A.scheme ⊗ U).hom := by
    change LocallyOfFiniteType
      (pullback.fst A.scheme.hom (𝟙 (Spec (.of k))) ≫ A.scheme.hom)
    infer_instance
  let : IsLocallyNoetherian (A.scheme ⊗ U).left :=
    LocallyOfFiniteType.isLocallyNoetherian (A.scheme ⊗ U).hom
  let D := RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L
  let C := RigidifiedConstantLine.Geometric.relativeRigidifiedConstant A N U
  let Z := RelativeComparison.Geometric.relativePicardComparison P D C
  let : LocallyOfFiniteType Z.hom :=
    inferInstanceAs (LocallyOfFiniteType (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroSchemeOver (RelativeComparison.Geometric.relativeComparisonLine D C) P).hom)
  obtain ⟨aK, haK⟩ := h
  let a := A.baseChangePointsEquiv b V aK
  have hleft := DifferenceBaseChangeValues.Geometric.relativeDifference_value_baseChange A L b V aK
  have hright : AbelianModuli.HilbertConstruction.Homogeneous.BaseChange.picardBaseChangeEquiv A.scheme b V
      ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard (A.pullback b).scheme).app (.op V)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((N.pullback (pullback.fst A.scheme.hom b)).pullback
          (snd V (A.pullback b).scheme).left))) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op W)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (N.pullback (snd W A.scheme).left)) :=
    (AbelianModuli.HilbertConstruction.Picard.BaseChange.toRelativePicard_baseChange_apply A.scheme b V _).trans
      (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op W))
        (ReferenceLineTranslation.Geometric.originalLineFamily_baseChange_class A b V N))
  have he : D.relativeValue a = C.relativeValue t :=
    hleft.symm.trans ((congrArg (AbelianModuli.HilbertConstruction.Homogeneous.BaseChange.picardBaseChangeEquiv A.scheme b V) haK).trans
      (hright.trans (RigidifiedConstantLine.Geometric.relativeRigidifiedConstant_value A N t).symm))
  obtain ⟨z, _, _⟩ := (RelativeComparison.Geometric.relativePicardComparison_factorization P D C a t).mp he
  let : Nonempty Z.left := ⟨z.left (IsLocalRing.closedPoint K)⟩
  let : Surjective Z.hom := ⟨Function.surjective_to_subsingleton _⟩
  obtain ⟨p, hp⟩ := FormalGeometry.Completion.RationalPointLift.Construction.exists_rationalPoint_lift Z.hom (𝟙 (Spec (.of k)))
  let z₀ : U ⟶ Z := Over.homMk p hp
  have hv := RelativeComparison.Geometric.relativePicardComparison_value P D C z₀
  have ht : z₀ ≫ RelativeComparison.Geometric.relativePicardComparisonProjection P D C = 𝟙 U := by
    apply Over.OverMorphism.ext
    have hbase : (z₀ ≫ RelativeComparison.Geometric.relativePicardComparisonProjection P D C).left ≫
        (𝟙 (Spec (.of k))) = 𝟙 (Spec (.of k)) :=
      (z₀ ≫ RelativeComparison.Geometric.relativePicardComparisonProjection P D C).w
    exact (Category.comp_id _).symm.trans hbase
  rw [ht] at hv
  exact ⟨z₀ ≫ RelativeComparison.Geometric.relativePicardComparisonParameter P D C,
    hv.trans (RigidifiedConstantLine.Geometric.relativeRigidifiedConstant_value A N (𝟙 U))⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldLineRealizationReflection.Geometric
