import OAI.AlgebraicGeometry.Comparison.Betti.UnramifiedChartGermNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.UnramifiedGermFlatness
import Mathlib.RingTheory.RingHom.StandardSmooth

/-! # Chart Germ Flatness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartGermFlatness.AnalyticLocal

noncomputable section

/-! Actual evaluation in a regular affine chart is flat when the
algebra has étale coordinates of the chart dimension. In particular
this holds for every standard smooth algebra of that dimension. -/

variable {A : Type} [CommRing A] [Algebra ℂ A] {n : ℕ}

theorem affineChartGermMap_flat_of_etale_coordinates
    (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (hf : f.toRingHom.Etale)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source) :
    (ChartGermMap.AnalyticLocal.affineChartGermMap e he x hx).Flat := by
  let : Algebra (MvPolynomial (Fin n) ℂ) A := f.toRingHom.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin n) ℂ) A := hf
  obtain ⟨q, hq, hqd, hqi, hnorm⟩ := UnramifiedChartGermNormalization.AnalyticLocal.exists_unramified_chart_germ_factorization f
    hf.formallyUnramified e he x hx
  apply UnramifiedGermFlatness.AnalyticLocal.flat_of_unramified_composite (R := MvPolynomial (Fin n) ℂ)
  change ((ChartGermMap.AnalyticLocal.affineChartGermMap e he x hx).comp f.toRingHom).Flat
  rw [← hnorm]
  exact RingHom.Flat.respectsIso.1 (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap (q (e x)))
    (LocalGermEquivRepresentatives.Analytic.localHolomorphicGermEquiv q hqd hqi (e x) hq).symm (MultivariableGermFlatness.AnalyticLocal.mvPolynomialGermMap_flat n (q (e x)))

theorem standardSmooth_affineChartGermMap_flat
    [Algebra.IsStandardSmoothOfRelativeDimension n ℂ A]
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source) :
    (ChartGermMap.AnalyticLocal.affineChartGermMap e he x hx).Flat := by
  obtain ⟨f, hf⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n ℂ A
  exact affineChartGermMap_flat_of_etale_coordinates f hf e he x hx

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartGermFlatness.AnalyticLocal
