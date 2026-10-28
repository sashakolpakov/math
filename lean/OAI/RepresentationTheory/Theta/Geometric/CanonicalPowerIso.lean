import OAI.RepresentationTheory.Theta.Geometric.PowerGaugeGluing

/-! # Canonical Power Iso -/

namespace OAI.RepresentationTheory.Theta.Geometric.CanonicalPowerIso

noncomputable section

/-! The canonical common-power projective map supplies every gauge needed
for the actual algebraic quotient-power isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

theorem canonicalThetaQuotientPower_iso [LocallyOfFiniteType X.hom] [IsReduced X.left]
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hF : 0 < F.degree) (hdeg : G.degree = F.degree + 1)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.commonPower G).projectiveDimension))
    (fF : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (fG : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hsurj : Function.Surjective e)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.commonPower G).projectiveDimension ((F.commonPower G).projectiveMap t))
    (heF : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map fF (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap t))
    (heG : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map fG (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension (G.projectiveMap t)) :
    Nonempty (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule (AlgebraicQuotient.algebraicThetaQuotient fF.left fG.left).sheaf F.degree ≅
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback fF.left (AlgebraicQuotient.algebraicTwistBundle F.projectiveDimension 1)).sheaf) := by
  have hG : 0 < G.degree := by omega
  let U : Fin (F.projectiveDimension + 1) × Fin (G.projectiveDimension + 1) → X.left.Opens :=
    fun p => PowerGauge.thetaPowerGaugeOpen F G f p.1 p.2
  have hU : iSup U = ⊤ := by
    rw [iSup_prod]
    exact PowerGaugeCover.thetaPowerGaugeOpen_cover F G f e he hsurj hF hG
  have hUf : ∀ p, U p ≤ fF.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) p.1 := by
    intro p
    exact (le_of_eq (PowerGaugeCover.thetaPowerGaugeOpen_eq F G f e he hsurj hF hG fF fG heF heG p.1 p.2)).trans inf_le_left
  have hUg : ∀ p, U p ≤ fG.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) p.2 := by
    intro p
    exact (le_of_eq (PowerGaugeCover.thetaPowerGaugeOpen_eq F G f e he hsurj hF hG fF fG heF heG p.1 p.2)).trans inf_le_right
  have hWF : ∀ p q, U p ⊓ U q ≤ fF.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) p.1 q.1 := by
    intro p q
    rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]
    exact le_inf (inf_le_left.trans (hUf p)) (inf_le_right.trans (hUf q))
  have hWG : ∀ p q, U p ⊓ U q ≤ fG.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) p.2 q.2 := by
    intro p q
    rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]
    exact le_inf (inf_le_left.trans (hUg p)) (inf_le_right.trans (hUg q))
  apply PowerGaugeGluing.thetaQuotientPower_iso_of_gauges fF.left fG.left F.degree U hU hUf hUg
    (fun p => PowerGauge.thetaPowerGaugeUnit F G f p.1 p.2) hWF hWG
  intro p q
  have h := PowerGaugeCover.thetaPowerGaugeUnit_transition F G hF hG f fF fG e hsurj he heF heG
    p.1 q.1 p.2 q.2 (U p ⊓ U q) inf_le_left inf_le_right (hWF p q) (hWG p q)
  simpa only [hdeg] using h

end

end OAI.RepresentationTheory.Theta.Geometric.CanonicalPowerIso
