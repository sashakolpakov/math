import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

/-! # Regular Chart Restriction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.RegularChartRestriction

/-! Shrinking the source of a native regular chart preserves its defining regular formulas. -/

open scoped ContDiff

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold

variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}

theorem affineRegularAtlas_restrOpen
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin d → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A d) (S : Set (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)) (hS : IsOpen S) :
    e.restrOpen S hS ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A d := by
  refine ⟨fun a => (he.1 a).mono Set.inter_subset_left, ?_⟩
  obtain ⟨g, hg, hc⟩ := he.2
  refine ⟨g, fun x hx => hg x hx.1, ?_⟩
  intro i
  obtain ⟨a, k, h⟩ := hc i
  exact ⟨a, k, fun x hx => h x hx.1⟩

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.RegularChartRestriction
