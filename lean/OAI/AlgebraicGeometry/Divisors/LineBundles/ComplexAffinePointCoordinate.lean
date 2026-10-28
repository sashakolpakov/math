import OAI.AlgebraicGeometry.Divisors.LineBundles.ComplexAffinePoints
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Space

/-! # Complex Affine Point Coordinate -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ComplexAffinePointCoordinate.BundleCycles

noncomputable section

/-! The continuous parameter point has exactly its stated complex
coordinate under the native scheme-point and global-section maps. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem complexAffineLinePoint_left (a : ℂ) :
    (ComplexAffinePoints.BundleCycles.complexAffineLinePoint a).left =
      Spec.map (CommRingCat.ofHom (Polynomial.aeval a : Polynomial ℂ →ₐ[ℂ] ℂ).toRingHom) ≫
        (LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv ℂ).hom := by
  change (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (Polynomial ℂ) (Polynomial.aeval a)).left ≫
    ComplexAffinePoints.BundleCycles.complexLinePolynomialOverIso.hom.left = _
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left]
  rfl

theorem complexAffineLinePoint_coordinate (a : ℂ) :
    (ComplexAffinePoints.BundleCycles.complexAffineLinePoint a).left.appTop (AffineLine.Space.BundleCycles.affineLineCoordinate Foundations.Scheme.ProjectiveSpace.complexBase) =
      (Scheme.ΓSpecIso (.of ℂ)).inv a := by
  rw [complexAffineLinePoint_left]
  change (Spec.map (CommRingCat.ofHom (Polynomial.aeval a : Polynomial ℂ →ₐ[ℂ] ℂ).toRingHom)).appTop
    ((LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv ℂ).hom.appTop (AffineLine.Space.BundleCycles.affineLineCoordinate (Spec (.of ℂ)))) = _
  rw [AffineLine.Space.BundleCycles.polynomialAffineSpaceEquiv_coordinate]
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.aeval a : Polynomial ℂ →ₐ[ℂ] ℂ).toRingHom)) Polynomial.X
  change (Scheme.ΓSpecIso (.of ℂ)).inv ((Polynomial.aeval a : Polynomial ℂ →ₐ[ℂ] ℂ) Polynomial.X) =
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval a : Polynomial ℂ →ₐ[ℂ] ℂ).toRingHom)).appTop
      (AffineLine.Space.BundleCycles.polynomialCoordinateSection ℂ) at h
  rw [Polynomial.aeval_X] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ComplexAffinePointCoordinate.BundleCycles
