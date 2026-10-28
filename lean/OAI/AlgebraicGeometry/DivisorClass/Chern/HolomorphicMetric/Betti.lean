import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Integration
import OAI.AlgebraicGeometry.DivisorClass.Chern.ReferenceHodgeHolomorphicBundles
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalIntegrationDefect

/-! # Betti -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Betti

noncomputable section

/-! Actual metric curvature represents the original rational Hodge class through the original Betti comparison. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalIntegrationDefect.CM.Construction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicRationalSmoothClass_eq (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) (a : V.rationalCohomology n) :
    ComplexMultiplication.HodgeComparison.RationalCohomologyMap.CM.Construction.rationalComplexCohomologyMap (ComplexMultiplication.HodgeComparison.RationalSmoothCech.CM.Construction.rationalSmoothCochainMap V.analyticModel V.analyticSpace) n a =
      V.rationalToSmoothSingular n a := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace V.toOver) n a
  exact (ComplexMultiplication.HodgeComparison.RationalCohomologyMap.CM.Construction.rationalComplexCohomologyMap_class (ComplexMultiplication.HodgeComparison.RationalSmoothCech.CM.Construction.rationalSmoothCochainMap V.analyticModel V.analyticSpace) n c).trans
    (ComplexMultiplication.HodgeComparison.RationalIntegrationDefect.CM.Construction.rationalSmoothCocycle_class V n c)

def holomorphicMetricClosedForm (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : Data.HolomorphicLineMetricData u) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 2 :=
  ⟨h.normalizedCurvature, h.normalizedCurvature_closed⟩

theorem holomorphicMetric_deRhamBettiClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : Data.HolomorphicLineMetricData u) :
    (V.deRhamBettiIso 2).hom (V.deRhamClass 2 (holomorphicMetricClosedForm V h)) =
      V.rationalCohomologyInclusion 2 (Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace u) := by
  apply (V.deRhamBettiIso_apply_eq_iff 2 _ _).mpr
  exact (V.deRhamToSmoothSingular_formClass 2 (holomorphicMetricClosedForm V h)).trans
    ((AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap V.analyticModel V.analyticSpace) 2
      h.curvatureCocycle).symm.trans (h.curvature_smooth_chern.trans
        (holomorphicRationalSmoothClass_eq V 2 (Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace u))))

theorem originalHodgeMetric_deRhamBettiClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : V.rationalCohomology 2) (ha : V.IsRationalHodgeClass 1 a)
    (h : Data.HolomorphicLineMetricData (ReferenceHodgeHolomorphicBundles.originalHodgeHolomorphicUnitClass V a ha)) :
    (V.deRhamBettiIso 2).hom (V.deRhamClass 2 (holomorphicMetricClosedForm V h)) =
      V.rationalCohomologyInclusion 2 (ReferenceHodgeHolomorphicBundles.originalHodgeIntegralMultiple V a ha • a) :=
  (holomorphicMetric_deRhamBettiClass V h).trans
    (congrArg (V.rationalCohomologyInclusion 2) (ReferenceHodgeHolomorphicBundles.originalHodgeHolomorphicUnitClass_chern V a ha))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Betti
