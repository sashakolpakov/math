import OAI.RepresentationTheory.Theta.Geometric.TransformedGaugeTransitions
import OAI.RepresentationTheory.Theta.Geometric.TranslatedHyperplaneGluing

/-! # Transformed Hyperplane Iso -/

namespace OAI.RepresentationTheory.Theta.Geometric.TransformedHyperplaneIso

noncomputable section

/-! The enlarged theta embedding supplies all regular gauges needed to
identify the translated and original hyperplane pullbacks algebraically. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

theorem transformedThetaHyperplane_iso [LocallyOfFiniteType X.hom] [IsReduced X.left]
    (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (T : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree → AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree) (a : Φ.space) (c : Φ.space → ℂ)
    (hc : ∀ z, c z ≠ 0) (hT : ∀ i z, T (F.coordinate i) z = c z ^ F.degree * F.coordinate i (z + a))
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.withSectionMap T).projectiveDimension))
    (f₀ f₁ : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hsurj : Function.Surjective e)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.withSectionMap T).projectiveDimension ((F.withSectionMap T).projectiveMap t))
    (he₀ : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f₀ (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap t))
    (he₁ : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f₁ (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap (t + QuotientAddGroup.mk a))) :
    Nonempty ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f₁.left (AlgebraicQuotient.algebraicTwistBundle F.projectiveDimension 1)).sheaf ≅
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f₀.left (AlgebraicQuotient.algebraicTwistBundle F.projectiveDimension 1)).sheaf) := by
  let U : Fin (F.projectiveDimension + 1) × Fin (F.projectiveDimension + 1) → X.left.Opens :=
    fun p => TransformedGauge.transformedThetaGaugeOpen F T f p.1 p.2
  have hU : iSup U = ⊤ := by
    rw [iSup_prod]
    exact TransformedGaugeCover.transformedThetaGaugeOpen_cover F T a c hc hT f e hsurj he
  have hU₀ : ∀ p, U p ≤ f₀.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) p.1 := fun p =>
    (le_of_eq (TransformedGaugeCover.transformedThetaGaugeOpen_eq F T a c hc hT f f₀ f₁ e hsurj he he₀ he₁ p.1 p.2)).trans inf_le_left
  have hU₁ : ∀ p, U p ≤ f₁.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) p.2 := fun p =>
    (le_of_eq (TransformedGaugeCover.transformedThetaGaugeOpen_eq F T a c hc hT f f₀ f₁ e hsurj he he₀ he₁ p.1 p.2)).trans inf_le_right
  have hW₀ : ∀ p q, U p ⊓ U q ≤ f₀.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) p.1 q.1 := by
    intro p q
    rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]
    exact le_inf (inf_le_left.trans (hU₀ p)) (inf_le_right.trans (hU₀ q))
  have hW₁ : ∀ p q, U p ⊓ U q ≤ f₁.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) p.2 q.2 := by
    intro p q
    rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]
    exact le_inf (inf_le_left.trans (hU₁ p)) (inf_le_right.trans (hU₁ q))
  apply TranslatedHyperplaneGluing.hyperplane_iso_of_comparison_gauges f₀.left f₁.left U hU hU₀ hU₁
    (fun p => TransformedGauge.transformedThetaGaugeUnit F T f p.1 p.2) hW₀ hW₁
  intro p q
  exact TransformedGaugeTransitions.transformedThetaGaugeUnit_transition F T a c hT f f₀ f₁ e hsurj he he₀ he₁
    p.1 q.1 p.2 q.2 (U p ⊓ U q) inf_le_left inf_le_right (hW₀ p q) (hW₁ p q)

end

end OAI.RepresentationTheory.Theta.Geometric.TransformedHyperplaneIso
