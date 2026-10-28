import OAI.RepresentationTheory.Theta.Geometric.DifferenceBundleNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace

/-! # Abelian Difference Bundle -/

namespace OAI.RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle

noncomputable section

/-! The actual difference bundle on an abelian variety's square is
normalized along both identity axes and satisfies the tensor formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)

def abelianDifferenceBundle (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A.scheme ⊗ A.scheme).left :=
  AlgebraicDifferenceBundle.algebraicDifferenceBundle L (fst A.scheme A.scheme).left (snd A.scheme A.scheme).left μ[A.scheme].left

theorem abelianDifferenceBundle_formula (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) :
    Nonempty (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (abelianDifferenceBundle A L).sheaf (L.pullback (fst A.scheme A.scheme).left).sheaf)
      (L.pullback (snd A.scheme A.scheme).left).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf) :=
  AlgebraicDifferenceBundle.algebraicDifferenceBundle_formula L _ _ _

theorem abelianDifferenceBundle_normalized_left (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) :
    Nonempty (((abelianDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left) := by
  apply DifferenceBundleNormalization.algebraicDifferenceBundle_axis_left A.scheme.hom η[A.scheme].left L
    (LineBundleFieldTriviality.lineBundle_over_field_trivial ℂ (L.pullback η[A.scheme].left))
  · exact congrArg Over.Hom.left (lift_fst (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme))
  · exact (congrArg Over.Hom.left (lift_snd (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme))).trans
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.one_point_left A A.scheme)
  · have h : lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme) ≫ μ[A.scheme] = 𝟙 A.scheme := by
      change (𝟙 A.scheme) * (1 : A.scheme ⟶ A.scheme) = 𝟙 A.scheme
      exact mul_one _
    exact congrArg Over.Hom.left h

theorem abelianDifferenceBundle_normalized_right (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) :
    Nonempty (((abelianDifferenceBundle A L).pullback
      (lift (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left) := by
  apply DifferenceBundleNormalization.algebraicDifferenceBundle_axis_right A.scheme.hom η[A.scheme].left L
    (LineBundleFieldTriviality.lineBundle_over_field_trivial ℂ (L.pullback η[A.scheme].left))
  · exact (congrArg Over.Hom.left (lift_fst (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme))).trans
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.one_point_left A A.scheme)
  · exact congrArg Over.Hom.left (lift_snd (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme))
  · have h : lift (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme) ≫ μ[A.scheme] = 𝟙 A.scheme := by
      change (1 : A.scheme ⟶ A.scheme) * (𝟙 A.scheme) = 𝟙 A.scheme
      exact one_mul _
    exact congrArg Over.Hom.left h

end

end OAI.RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle
