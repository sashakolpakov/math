import OAI.RepresentationTheory.Theta.Geometric.DifferenceBundleNormalization
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme

/-! # Relative Difference Bundle -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric

noncomputable section

/-! Normalize an actual line bundle along the identity section of a
varying abelian family. Its actual difference bundle then has both
identity normalizations over the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.RepresentationTheory.Theta.Geometric.DifferenceBundleNormalization OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

def identityNormalizedLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left :=
  L.tensor (Homomorphisms.LineBundleDual.Construction.lineBundleDual ((L.pullback η[A.scheme].left).pullback A.scheme.hom))

theorem identityNormalizedLine_axis :
    Nonempty (((identityNormalizedLine A L).pullback η[A.scheme].left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S) := by
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((identityNormalizedLine A L).pullback η[A.scheme].left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass S := by
    let e : S ⟶ A.scheme.left := η[A.scheme].left
    have he : e ≫ A.scheme.hom = 𝟙 S := η[A.scheme].w
    change RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback e (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L *
      (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback A.scheme.hom (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback e (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)))⁻¹) = 1
    rw [map_mul, map_inv, RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp, he, RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_id, mul_inv_cancel]
  exact Quotient.exact he

def relativeDifferenceBundle : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A.scheme ⊗ A.scheme).left :=
  RepresentationTheory.Theta.Geometric.AlgebraicDifferenceBundle.algebraicDifferenceBundle (identityNormalizedLine A L)
    (fst A.scheme A.scheme).left (snd A.scheme A.scheme).left μ[A.scheme].left

theorem relativeDifferenceBundle_normalized_left :
    Nonempty (((relativeDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left) := by
  apply RepresentationTheory.Theta.Geometric.DifferenceBundleNormalization.algebraicDifferenceBundle_axis_left A.scheme.hom η[A.scheme].left
    (identityNormalizedLine A L) (identityNormalizedLine_axis A L)
  · exact congrArg Over.Hom.left (lift_fst (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme))
  · exact (congrArg Over.Hom.left (lift_snd (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme))).trans
      (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.one_point_left A A.scheme)
  · have h : lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme) ≫ μ[A.scheme] = 𝟙 A.scheme := by
      change (𝟙 A.scheme) * (1 : A.scheme ⟶ A.scheme) = 𝟙 A.scheme
      exact mul_one _
    exact congrArg Over.Hom.left h

theorem relativeDifferenceBundle_normalized_right :
    Nonempty (((relativeDifferenceBundle A L).pullback
      (lift (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left) := by
  apply RepresentationTheory.Theta.Geometric.DifferenceBundleNormalization.algebraicDifferenceBundle_axis_right A.scheme.hom η[A.scheme].left
    (identityNormalizedLine A L) (identityNormalizedLine_axis A L)
  · exact (congrArg Over.Hom.left (lift_fst (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme))).trans
      (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.one_point_left A A.scheme)
  · exact congrArg Over.Hom.left (lift_snd (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme))
  · have h : lift (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme) ≫ μ[A.scheme] = 𝟙 A.scheme := by
      change (1 : A.scheme ⟶ A.scheme) * (𝟙 A.scheme) = 𝟙 A.scheme
      exact one_mul _
    exact congrArg Over.Hom.left h

def relativeRigidifiedDifference : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A.scheme A.scheme where
  bundle := relativeDifferenceBundle A L
  axis := Classical.choice (relativeDifferenceBundle_normalized_left A L)

theorem relativeDifferenceBundle_formula :
    Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (relativeDifferenceBundle A L).sheaf
        ((identityNormalizedLine A L).pullback (fst A.scheme A.scheme).left).sheaf)
      ((identityNormalizedLine A L).pullback (snd A.scheme A.scheme).left).sheaf ≅
        ((identityNormalizedLine A L).pullback μ[A.scheme].left).sheaf) :=
  RepresentationTheory.Theta.Geometric.AlgebraicDifferenceBundle.algebraicDifferenceBundle_formula (identityNormalizedLine A L) _ _ _

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric
