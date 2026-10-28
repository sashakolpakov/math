import OAI.AlgebraicGeometry.Comparison.Betti.SeparatingCovectorsSpan
import OAI.AlgebraicGeometry.Comparison.Betti.SpanningFamilyBasis
import OAI.AlgebraicGeometry.Cycles.Functoriality.EtaleDifferential

/-! # Regular Differentials Span -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.RegularDifferentialsSpan

noncomputable section

/-! Actual differentials of regular functions span the cotangent space in every native affine chart. -/

open scoped ContDiff

variable {A : Type} [CommRing A] [Algebra ℂ A] {n : ℕ}

theorem affineRegularChart_differentials_span
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source) :
    Submodule.span ℂ (Set.range (fun a : A =>
      (fderiv ℂ (fun z => e.symm z a) (e x)).toLinearMap)) = ⊤ := by
  apply SeparatingCovectorsSpan.LinearAlgebra.covectors_span_of_separating
  intro v hv
  exact Cycles.Functoriality.EtaleDifferential.Construction.affineRegularChart_tangent_eq_zero e he x hx v hv

theorem affineRegularChart_exists_differentialBasis
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source) :
    ∃ (s : Set (Module.Dual ℂ (Fin n → ℂ)))
      (b : Module.Basis s ℂ (Module.Dual ℂ (Fin n → ℂ))) (a : s → A),
        ∀ i, b i = (fderiv ℂ (fun z => e.symm z (a i)) (e x)).toLinearMap :=
  SpanningFamilyBasis.LinearAlgebra.exists_basis_subfamily_of_span _
    (affineRegularChart_differentials_span e he x hx)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.RegularDifferentialsSpan
