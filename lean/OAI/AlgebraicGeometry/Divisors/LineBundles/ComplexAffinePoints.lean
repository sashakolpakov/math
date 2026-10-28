import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.OverProduct
import Mathlib.Topology.Algebra.Polynomial

/-! # Complex Affine Points -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ComplexAffinePoints.BundleCycles

noncomputable section

/-! A continuous complex parameter gives the actual affine-line point,
via polynomial evaluation and the native affine-character correspondence. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

def complexLinePolynomialOverIso : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Polynomial ℂ) ≅ AffineLine.OverProduct.BundleCycles.complexAffineLineOver :=
  Over.isoMk (LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv ℂ) (LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv_over ℂ)

def complexAffineLinePoint (a : ℂ) : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints AffineLine.OverProduct.BundleCycles.complexAffineLineOver :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (Polynomial ℂ))
    complexLinePolynomialOverIso.hom (Polynomial.aeval a)

theorem complexAffineLinePoint_continuous : Continuous complexAffineLinePoint := by
  have hc : Continuous (fun a : ℂ => (Polynomial.aeval a : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Polynomial ℂ))) := by
    apply (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff _).mpr
    intro p
    exact p.continuous_aeval
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap (CommAlgCat.of ℂ (Polynomial ℂ))
    complexLinePolynomialOverIso.hom).comp hc

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ComplexAffinePoints.BundleCycles
