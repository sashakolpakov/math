import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartGermMap
import OAI.AlgebraicGeometry.Comparison.Betti.PolynomialCoordinateChart
import OAI.AlgebraicGeometry.Comparison.Betti.LocalGermEquivRepresentatives
import OAI.AlgebraicGeometry.Comparison.Betti.MultivariablePolynomialGerms
import OAI.AlgebraicGeometry.Cycles.Functoriality.AnalyticInverse

/-! # Unramified Chart Germ Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.UnramifiedChartGermNormalization.AnalyticLocal

noncomputable section

/-! Unramified coordinates give an actual local biholomorphism whose
germ pullback is exactly algebraic polynomial evaluation in the chart. -/

open Set Filter
open scoped _root_.Topology ContDiff

theorem exists_unramified_chart_germ_factorization {A : Type} [CommRing A] [Algebra ℂ A] {n : ℕ}
    (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (hf : f.toRingHom.FormallyUnramified)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source) :
    ∃ (q : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ))
      (hq : e x ∈ q.source) (hqd : DifferentiableOn ℂ q q.source)
      (hqi : DifferentiableOn ℂ q.symm q.target),
      ((LocalGermEquivRepresentatives.Analytic.localHolomorphicGermEquiv q hqd hqi (e x) hq).symm.toRingHom).comp
        (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap (q (e x))) = (Affine.ChartGermMap.AnalyticLocal.affineChartGermMap e he x hx).comp f.toRingHom := by
  obtain ⟨q, hxq, hq, hqd, hqi⟩ := Cycles.Functoriality.AnalyticInverse.Construction.exists_unramified_affineChart_localInverse
    f hf e (PolynomialCoordinateChart.AnalyticLocal.polynomialCoordinateChart n) he (PolynomialCoordinateChart.AnalyticLocal.polynomialCoordinateChart_mem_atlas n) x hx (by trivial)
  refine ⟨q, hxq, hqd.differentiableOn (by simp), hqi.differentiableOn (by simp), ?_⟩
  apply RingHom.ext
  intro P
  apply Subtype.ext
  change ((LocalGermEquivRepresentatives.Analytic.localHolomorphicGermEquiv q (hqd.differentiableOn (by simp))
    (hqi.differentiableOn (by simp)) (e x) hxq).symm (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap (q (e x)) P)).val =
    (Affine.ChartGermMap.AnalyticLocal.affineChartGermMap e he x hx (f P)).val
  erw [LocalGermEquivRepresentatives.Analytic.localHolomorphicGermEquiv_symm_val, MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap_val, Affine.ChartGermMap.AnalyticLocal.affineChartGermMap_val]
  apply Germ.coe_eq.mpr
  apply Eventually.of_forall
  intro z
  change MvPolynomial.eval (q z) P = e.symm z (f P)
  rw [hq]
  exact PolynomialCoordinateChart.AnalyticLocal.polynomialCoordinateChart_eval n ((e.symm z).comp f) P

end

end OAI.AlgebraicGeometry.Comparison.Betti.UnramifiedChartGermNormalization.AnalyticLocal
