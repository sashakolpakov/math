import OAI.RepresentationTheory.Theta.Geometric.IsoGaugeCompatibility
import OAI.RepresentationTheory.Theta.Geometric.IsoGaugeHolomorphic
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.Gluing

/-! # Iso Global Gauge -/

namespace OAI.RepresentationTheory.Theta.Geometric.IsoGlobalGauge

noncomputable section

/-! An actual native theta-quotient isomorphism yields a global nonzero
holomorphic translation comparison with the original automorphy factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold

theorem exists_holomorphic_translationGauge_of_theta_iso
    {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
    {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hdeg : G.degree = F.degree + 1)
    (fS fT : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (gS gT : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (e : (AlgebraicQuotient.algebraicThetaQuotient fS.left gS.left).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient fT.left gT.left).sheaf)
    (a : Φ.space) (p : Φ.space → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hp : MDifferentiable (𝓘(ℂ, Φ.space))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p)
    (hperiod : ∀ l : Φ.periodIntegerLattice, ∀ z, p (z + l.val) = p z)
    (hfS : ∀ z, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map fS (p z) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk (z + a))))
    (hgS : ∀ z, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map gS (p z) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap (QuotientAddGroup.mk (z + a))))
    (hfT : ∀ z, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map fT (p z) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk z)))
    (hgT : ∀ z, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map gT (p z) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap (QuotientAddGroup.mk z))) :
    ∃ c : Φ.space → ℂ, Differentiable ℂ c ∧ (∀ z, c z ≠ 0) ∧
      ∀ (l : Φ.periodIntegerLattice) (z : Φ.space),
        c (z + l.val) * J.value l (z + a) = J.value l z * c z := by
  have hmem (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension ×
      QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension) (z : Φ.space)
      (hi : z ∈ GaugeOpens.thetaTranslationGaugeOpen F G a i) :
      (p z).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ IsoFrameUnits.thetaIsoFrameOpen fS.left fT.left gS.left gT.left i :=
    (IsoGaugeCompatibility.thetaIsoFrameOpen_mem F G fS fT gS gT (p z) (z + a) z (hfS z) (hgS z) (hfT z) (hgT z) i).mpr hi
  obtain ⟨c, hc, hmatch⟩ := Holomorphic.Gluing.exists_differentiable_gluing (GaugeOpens.thetaTranslationGaugeOpen F G a)
    (fun i z => IsoGaugeCompatibility.localThetaIsoGauge F G fS fT gS gT e i (p z) (z + a) z)
    (GaugeOpens.thetaTranslationGaugeOpen_isOpen F G a) (GaugeOpens.thetaTranslationGaugeOpen_cover F G a)
    (fun i z hi => IsoGaugeHolomorphic.localThetaIsoGauge_differentiableAt F G fS fT gS gT e a p i z (hp z) (hmem i z hi) hi)
    (fun i j z hi hj => IsoGaugeCompatibility.localThetaIsoGauge_compatible F G fS fT gS gT e (p z) (z + a) z
      (hfS z) (hgS z) (hfT z) (hgT z) i j (hmem i z hi) (hmem j z hj))
  refine ⟨c, hc, ?_, ?_⟩
  · intro z
    obtain ⟨i, hi⟩ := GaugeOpens.thetaTranslationGaugeOpen_cover F G a z
    rw [hmatch i z hi]
    exact IsoGaugeCompatibility.localThetaIsoGauge_ne_zero F G fS fT gS gT e i (p z) (z + a) z (hmem i z hi)
      (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero F G i.1.1 i.1.2 (z + a) hi.1.1 hi.1.2)
      (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero F G i.2.1 i.2.2 z hi.2.1 hi.2.2)
  · intro l z
    obtain ⟨i, hi⟩ := GaugeOpens.thetaTranslationGaugeOpen_cover F G a z
    rw [hmatch i z hi,
      hmatch i (z + l.val) ((GaugeOpens.thetaTranslationGaugeOpen_translates F G a i l z).mpr hi)]
    exact IsoGaugeHolomorphic.localThetaIsoGauge_translates F G fS fT gS gT e a p hdeg hperiod i l z hi

end

end OAI.RepresentationTheory.Theta.Geometric.IsoGlobalGauge
