import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceLineTranslation
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.SameChernDifferenceValues

/-! # Difference Base Change Values -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceBaseChangeValues.Geometric

noncomputable section

/-! The original normalized difference map retains its full Picard
value under arbitrary base change, through the actual sheaf comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

private theorem map_difference_of_values
    {M N : Type*} [Group M] [Group N] (f : M →* N)
    (a b : M) (c d : N) (ha : f a = c) (hb : f b = d) :
    f (a * b⁻¹) = c * d⁻¹ := by
  rw [map_mul, map_inv, ha, hb]

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

theorem relativeDifference_value_original {U : Over S} (a : U ⟶ A.scheme) :
    (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
      (Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme U)
        (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation a).left
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd U A.scheme).left))) *
      ((Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme U)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd U A.scheme).left)))⁻¹ := by
  rw [RelativeDifferenceEq.Geometric.relativeRigidifiedDifference_value]
  have h := ReferenceLineTranslation.Geometric.originalLineFamily_picard_normalization A L U
  have ht := RelativeTranslationClasses.Geometric.translation_relativeClass_congr A a _ _ h
  exact congrArg₂ (fun x y => x * y⁻¹) ht h

theorem relativeDifference_value_original_class {U : Over S} (a : U ⟶ A.scheme) :
    (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
        (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation a).left
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd U A.scheme).left)) *
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd U A.scheme).left))⁻¹) := by
  rw [relativeDifference_value_original]
  let picardMap : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ A.scheme).left →* AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A.scheme U :=
    Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme U
  let q := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd U A.scheme).left)
  change picardMap (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation a).left q) * (picardMap q)⁻¹ =
    picardMap (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation a).left q * q⁻¹)
  rw [map_mul, map_inv]

theorem relativeDifference_value_baseChange {S' : Scheme} (f : S' ⟶ S) (U : Over S')
    (a : U ⟶ (A.pullback f).scheme) :
    AbelianModuli.HilbertConstruction.Homogeneous.BaseChange.picardBaseChangeEquiv A.scheme f U
      ((RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference (A.pullback f)
        (L.pullback (CategoryTheory.Limits.pullback.fst A.scheme.hom f))).relativeValue a) =
      (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue (A.baseChangePointsEquiv f U a) := by
  let B := A.pullback f
  let K : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.scheme.left :=
    L.pullback (CategoryTheory.Limits.pullback.fst A.scheme.hom f)
  let q := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (K.pullback (snd U B.scheme).left)
  let q₀ := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd ((Over.map f).obj U) A.scheme).left)
  let σ : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ B.scheme).left →*
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (((Over.map f).obj U) ⊗ A.scheme).left :=
    Homomorphisms.SchemePullback.Construction.schemePicardPullback (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme f U).inv
  let τ := RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation (A.baseChangePointsEquiv f U a)).left
  have hq : σ q = q₀ := ReferenceLineTranslation.Geometric.originalLineFamily_baseChange_class A f U L
  have ht : σ (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (B.translation a).left q) = τ q₀ :=
    (A.translationClass_baseChange f U a q).trans (congrArg τ hq)
  have hratio : σ (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (B.translation a).left q * q⁻¹) = τ q₀ * q₀⁻¹ :=
    map_difference_of_values σ _ _ _ _ ht hq
  have hstart := congrArg (AbelianModuli.HilbertConstruction.Homogeneous.BaseChange.picardBaseChangeEquiv A.scheme f U)
    (relativeDifference_value_original_class B K a)
  have hmiddle := AbelianModuli.HilbertConstruction.Picard.BaseChange.toRelativePicard_baseChange_apply A.scheme f U
    (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (B.translation a).left q * q⁻¹)
  have hend := relativeDifference_value_original_class A L (A.baseChangePointsEquiv f U a)
  exact hstart.trans (hmiddle.trans
    ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op ((Over.map f).obj U))) hratio).trans hend.symm))

theorem relativeDifference_value_native {d : ℕ} (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d Foundations.Scheme.ProjectiveSpace.complexBase)
    (K : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.scheme.left) {U : Over Foundations.Scheme.ProjectiveSpace.complexBase} (a : U ⟶ B.scheme) :
    (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference B K).relativeValue a =
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle B K) a := by
  rw [relativeDifference_value_original, SameChernDifferenceValues.Geometric.nativeDifference_picard_value]
  rfl

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceBaseChangeValues.Geometric
