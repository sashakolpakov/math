import OAI.RepresentationTheory.Theta.Geometric.Affine.TestMaps
import OAI.RepresentationTheory.Theta.Geometric.SquareZero.Ideal
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-! # Affine Factorization -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.AffineFactorization

noncomputable section

/-! An actual affine-scheme parameter constant modulo a square-zero
ideal factors through the associated split square-zero test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

attribute [local instance] SquareZero.Ideal.idealCoefficientOppositeModule SquareZero.Ideal.idealCoefficientCentralScalar

set_option backward.isDefEq.respectTransparency false in
theorem squareZero_affineTest_factorization
    {R : Type} [CommRing R] [Algebra ℂ R] [Nontrivial R]
    (I : Ideal R) (hI : I * I = ⊥) (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    (r : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ X) (e : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (h : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (R ⧸ I) (Ideal.Quotient.mkₐ ℂ I) ≫ r =
      toUnit (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (R ⧸ I)) ≫ e) :
    ∃ a : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ I) ⟶ X,
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ (TrivSqZeroExt ℂ I) R (SquareZero.Ideal.squareZeroIdealMap I hI) ≫ a = r := by
  let f := (Affine.TestMaps.affineTestMapEquiv X R).symm r
  let p := AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X e
  have hf : Affine.TestMaps.affineTestMapEquiv X R f = r := (Affine.TestMaps.affineTestMapEquiv X R).apply_symm_apply r
  have hp : (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X).symm p = e := (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X).symm_apply_apply e
  have hq : (Ideal.Quotient.mkₐ ℂ I).comp f = (Algebra.ofId ℂ (R ⧸ I)).comp p := by
    apply (Affine.TestMaps.affineTestMapEquiv X (R ⧸ I)).injective
    rw [← Affine.TestMaps.affineTestMapEquiv_comp, hf, Affine.TestMaps.affineTestMapEquiv_constant, hp]
    exact h
  obtain ⟨g, hg⟩ := SquareZero.Ideal.squareZeroIdeal_exists_factorization I hI f p (fun x => DFunLike.congr_fun hq x)
  refine ⟨Affine.TestMaps.affineTestMapEquiv X (TrivSqZeroExt ℂ I) g, ?_⟩
  rw [Affine.TestMaps.affineTestMapEquiv_comp, hg]
  exact hf

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.AffineFactorization
