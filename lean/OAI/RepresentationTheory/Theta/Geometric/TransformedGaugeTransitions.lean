import OAI.RepresentationTheory.Theta.Geometric.TransformedGaugeCover
import OAI.RepresentationTheory.Theta.Geometric.PowerGaugeCover

/-! # Transformed Gauge Transitions -/

namespace OAI.RepresentationTheory.Theta.Geometric.TransformedGaugeTransitions

noncomputable section

/-! The transformed-section gauges satisfy the exact native transition
identity for the translated hyperplane pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

theorem translatedTheta_projectiveTransitionUnit_value (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (a : Φ.space)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap (t + QuotientAddGroup.mk a)))
    (i k : Fin (F.projectiveDimension + 1)) (z : Φ.space)
    (hx : (e (QuotientAddGroup.mk z)).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈
      f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) :
    Complex.SectionEvaluation.complexSectionValue (e (QuotientAddGroup.mk z)).left
      (f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) hx
      (PowerGauge.projectivePullbackTransitionUnit f.left i k :
        Γ(X.left, f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)) =
      F.coordinate k (z + a) / F.coordinate i (z + a) := by
  have h := PowerGauge.projectivePullbackTransitionUnit_value f (e (QuotientAddGroup.mk z))
    (F.projectiveMap (QuotientAddGroup.mk (z + a))) (he (QuotientAddGroup.mk z)) i k hx
  rw [F.projectiveMap_coordinates] at h
  exact h

theorem transformedThetaGaugeUnit_transition [LocallyOfFiniteType X.hom] [IsReduced X.left]
    (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (T : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree → AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree) (a : Φ.space) (c : Φ.space → ℂ)
    (hT : ∀ i z, T (F.coordinate i) z = c z ^ F.degree * F.coordinate i (z + a))
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.withSectionMap T).projectiveDimension))
    (f₀ f₁ : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hsurj : Function.Surjective e)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.withSectionMap T).projectiveDimension ((F.withSectionMap T).projectiveMap t))
    (he₀ : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f₀ (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap t))
    (he₁ : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f₁ (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap (t + QuotientAddGroup.mk a)))
    (i k j l : Fin (F.projectiveDimension + 1)) (W : X.left.Opens)
    (hWij : W ≤ TransformedGauge.transformedThetaGaugeOpen F T f i j) (hWkl : W ≤ TransformedGauge.transformedThetaGaugeOpen F T f k l)
    (hW₀ : W ≤ f₀.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
    (hW₁ : W ≤ f₁.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) j l) :
    PowerGaugeCover.restrictRegularUnit hWkl (TransformedGauge.transformedThetaGaugeUnit F T f k l) *
        PowerGaugeCover.restrictRegularUnit hW₀ (PowerGauge.projectivePullbackTransitionUnit f₀.left i k) =
      PowerGaugeCover.restrictRegularUnit hWij (TransformedGauge.transformedThetaGaugeUnit F T f i j) *
        PowerGaugeCover.restrictRegularUnit hW₁ (PowerGauge.projectivePullbackTransitionUnit f₁.left j l) := by
  apply Units.ext
  apply Complex.PointsDetectSections.complexSectionValue_ext X W
  intro p hp
  obtain ⟨t, rfl⟩ := hsurj p
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective t
  have hij := (TransformedGaugeCover.transformedThetaGaugeOpen_mem F T f e he i j z).mp (hWij hp)
  have hkl := (TransformedGaugeCover.transformedThetaGaugeOpen_mem F T f e he k l z).mp (hWkl hp)
  have hj : F.coordinate j (z + a) ≠ 0 := by
    intro hz
    exact hij.2 (by rw [hT, hz, mul_zero])
  change Complex.SectionEvaluation.complexSectionValue _ W hp
      ((PowerGaugeCover.restrictRegularUnit hWkl (TransformedGauge.transformedThetaGaugeUnit F T f k l) : Γ(X.left, W)) *
        (PowerGaugeCover.restrictRegularUnit hW₀ (PowerGauge.projectivePullbackTransitionUnit f₀.left i k) : Γ(X.left, W))) =
    Complex.SectionEvaluation.complexSectionValue _ W hp
      ((PowerGaugeCover.restrictRegularUnit hWij (TransformedGauge.transformedThetaGaugeUnit F T f i j) : Γ(X.left, W)) *
        (PowerGaugeCover.restrictRegularUnit hW₁ (PowerGauge.projectivePullbackTransitionUnit f₁.left j l) : Γ(X.left, W)))
  rw [map_mul, map_mul, PowerGaugeCover.restrictRegularUnit_value, PowerGaugeCover.restrictRegularUnit_value,
    PowerGaugeCover.restrictRegularUnit_value, PowerGaugeCover.restrictRegularUnit_value,
    TransformedGauge.transformedThetaGaugeUnit_value F T f e he, TransformedGauge.transformedThetaGaugeUnit_value F T f e he,
    PowerGaugeCover.theta_projectiveTransitionUnit_value F f₀ e he₀,
    translatedTheta_projectiveTransitionUnit_value F a f₁ e he₁, hT, hT]
  field_simp [hij.1, hkl.1, hj]

end

end OAI.RepresentationTheory.Theta.Geometric.TransformedGaugeTransitions
