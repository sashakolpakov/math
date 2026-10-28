import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceLineValues
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceBaseChangeValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationFamilyMaps

/-! # Reference Difference Family Maps -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceDifferenceFamilyMaps.Geometric

noncomputable section

/-! Original normalized difference values depend only on the original
line class and commute with actual homomorphisms of abelian schemes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S : Scheme.{0}} {g h : ℕ}

theorem relativeDifference_value_class_congr (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)
    {U : Over S} (a : U ⟶ A.scheme) :
    (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a = (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A M).relativeValue a := by
  have hq := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd U A.scheme).left) hc
  exact (DifferenceBaseChangeValues.Geometric.relativeDifference_value_original_class A L a).trans
    ((congrArg (fun q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ A.scheme).left =>
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation a).left q * q⁻¹)) hq).trans
      (DifferenceBaseChangeValues.Geometric.relativeDifference_value_original_class A M a).symm)

theorem relativeDifference_value_familyMap (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.scheme.left)
    {U : Over S} (a : U ⟶ A.scheme) :
    (AbelianModuli.HilbertConstruction.Picard.FamilySheafMaps.relativePicardSheafMap f).hom.app (.op U)
      ((RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference B L).relativeValue (a ≫ f)) =
        (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A (L.pullback f.left)).relativeValue a := by
  let σ : (U ⊗ A.scheme).left ⟶ (U ⊗ B.scheme).left := (𝟙 U ⊗ₘ f).left
  let q := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd U B.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)
  let r := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd U A.scheme).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback f.left))
  have hs : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback σ q = r := ReferenceLineValues.Geometric.constantLineClass_familyMap A B f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) U
  have ht : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback σ (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (B.translation (a ≫ f)).left q) =
      RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation a).left (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback σ q) :=
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translationClass_familyMap f a q
  have hc : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback σ (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (B.translation (a ≫ f)).left q * q⁻¹) =
      RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (A.translation a).left r * r⁻¹ := by
    rw [map_mul, map_inv, ht, hs]
  exact (congrArg ((AbelianModuli.HilbertConstruction.Picard.FamilySheafMaps.relativePicardSheafMap f).hom.app (.op U))
    (DifferenceBaseChangeValues.Geometric.relativeDifference_value_original_class B L (a ≫ f))).trans
      ((AbelianModuli.HilbertConstruction.Picard.FamilySheafMaps.relativePicardSheafMap_toRelative f U _).trans
        ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)) hc).trans
          (DifferenceBaseChangeValues.Geometric.relativeDifference_value_original_class A (L.pullback f.left) a).symm))

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceDifferenceFamilyMaps.Geometric
