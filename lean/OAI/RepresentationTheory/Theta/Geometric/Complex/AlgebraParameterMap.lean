import OAI.RepresentationTheory.Theta.Geometric.Affine.TestMaps
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ProductOpenCover

/-! # Algebra Parameter Map -/

namespace OAI.RepresentationTheory.Theta.Geometric.Complex.AlgebraParameterMap

noncomputable section

/-! Native complex affine-test maps in a parameter algebra tower. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable (B R : Type) [CommRing B] [CommRing R] [Algebra ℂ B] [Algebra ℂ R]
    [Algebra B R] [IsScalarTower ℂ B R]

def complexAlgebraParameterMap : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B :=
  AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B R (IsScalarTower.toAlgHom ℂ B R)

theorem complexAlgebraParameterMap_left :
    (complexAlgebraParameterMap B R).left = Spec.map (CommRingCat.ofHom (algebraMap B R)) :=
  AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv_left ℂ B R (IsScalarTower.toAlgHom ℂ B R)

theorem complexAlgebraParameterMap_subalgebra_factor (S : Subalgebra B R) :
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R (S.val.restrictScalars ℂ) ≫ complexAlgebraParameterMap B S =
      complexAlgebraParameterMap B R := by
  change AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R _ ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B S _ = _
  rw [← Affine.TestMaps.affineAlgHomOverSpecEquiv_comp]
  rfl

theorem complexAlgebraParameterMap_product_isPullback (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    IsPullback (complexAlgebraParameterMap B R ▷ X).left (fst (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) X).left
      (fst (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B) X).left (Spec.map (CommRingCat.ofHom (algebraMap B R))) := by
  have H := AlgebraicGeometry.PELModuli.IntegralModel.Picard.ProductOpenCover.PicardProductOpenCover.productMap_isPullback X (complexAlgebraParameterMap B R)
  exact (congrArg (fun t => IsPullback (complexAlgebraParameterMap B R ▷ X).left
    (fst (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) X).left (fst (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B) X).left t)
      (complexAlgebraParameterMap_left B R)).mp H

end

end OAI.RepresentationTheory.Theta.Geometric.Complex.AlgebraParameterMap
