import OAI.RepresentationTheory.Theta.Geometric.Local.DualGaugeCompatibility
import OAI.RepresentationTheory.Theta.Geometric.Local.DualGaugeCovariance
import OAI.RepresentationTheory.Theta.Geometric.GaugeOpens

/-! # Global Dual Gauge -/

namespace OAI.RepresentationTheory.Theta.Geometric.GlobalDualGauge

noncomputable section

/-! An actual native infinitesimal theta-quotient isomorphism yields a
global holomorphic dual-number gauge with the exact first-jet automorphy
of the original theta factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold

theorem exists_globalDualThetaGauge
    {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
    {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hdeg : G.degree = F.degree + 1)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (g : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X ⟶ X)
    (e : (AlgebraicQuotient.algebraicThetaQuotient (t ≫ f).left (t ≫ g).left).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
        (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left).sheaf)
    (p : Φ.space → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (a : Φ.space)
    (ht : ∀ z, Dual.AffineBaseChangeChart.dualConstantPoint X (p z) ≫ t = Intrinsic.MapFirstJet.nativeMapFirstJet X p z a)
    (hf : ∀ w, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (p w) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk w)))
    (hg : ∀ w, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (p w) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap (QuotientAddGroup.mk w)))
    (hp : MDifferentiable (𝓘(ℂ, Φ.space))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p)
    (hperiod : ∀ (l : Φ.periodIntegerLattice) z, p (z + l.val) = p z)
    (hJ : ∀ l : Φ.periodIntegerLattice, Differentiable ℂ (J.value l)) :
    ∃ c : Φ.space → DualNumber ℂ, (∀ z, Dual.CoefficientHolomorphic.DualCoefficientDifferentiableAt c z) ∧
      (∀ z, IsUnit (c z)) ∧ ∀ (l : Φ.periodIntegerLattice) z,
        c (z + l.val) * ScalarFirstJet.scalarFirstJet (J.value l) z a = TrivSqZeroExt.inl (J.value l z) * c z := by
  have hmem (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension) (z : Φ.space)
      (hi : z ∈ GaugeOpens.thetaGaugeOpen F G i) :
      (Dual.BaseChangeReduction.dualBaseChangeReduction X).left ((p z).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈
        Dual.IsoCoefficients.dualThetaIsoFrameOpen f g t i :=
    (Dual.IsoCoordinates.dualThetaIsoFrameOpen_mem F G f g t (p z) z (Dual.SourceReduction.dualSource_reduction_eq X p z a t (ht z))
      (hf z) (hg z) i).mpr hi
  obtain ⟨c, hc, hmatch⟩ := Dual.CoefficientHolomorphic.exists_dualCoefficientDifferentiable_gluing (GaugeOpens.thetaGaugeOpen F G)
    (fun i z => Local.DualGauge.localDualThetaGauge F G f g t e i (p z) z a)
    (GaugeOpens.thetaGaugeOpen_isOpen F G) (GaugeOpens.thetaGaugeOpen_cover F G)
    (fun i z hi => Local.DualGauge.localDualThetaGauge_differentiableAt F G f g t e i p z a (hp z) (hmem i z hi) hi.1 hi.2)
    (fun i j z hi hj => Local.DualGaugeCompatibility.localDualThetaGauge_compatible F G f g t e p z a (ht z) hf hg (hp z) i j hi hj)
  refine ⟨c, hc, ?_, ?_⟩
  · intro z
    obtain ⟨i, hi⟩ := GaugeOpens.thetaGaugeOpen_cover F G z
    rw [hmatch i z hi]
    exact Local.DualGauge.localDualThetaGauge_isUnit F G f g t e i (p z) z a (hmem i z hi) hi.1 hi.2
  · intro l z
    obtain ⟨i, hi⟩ := GaugeOpens.thetaGaugeOpen_cover F G z
    rw [hmatch i z hi, hmatch i (z + l.val) ((GaugeOpens.thetaGaugeOpen_translates F G i l z).mpr hi)]
    exact Local.DualGaugeCovariance.localDualThetaGauge_translates F G hdeg f g t e p z a l (hperiod l z) (hJ l z) i
      (hmem i z hi) hi.1 hi.2

end

end OAI.RepresentationTheory.Theta.Geometric.GlobalDualGauge
