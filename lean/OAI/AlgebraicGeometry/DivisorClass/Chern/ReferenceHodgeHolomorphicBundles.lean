import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.BettiComplexSheaf
import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SmoothIntegration
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Lifting
import OAI.AlgebraicGeometry.Betti.ProjectivePresentationCohomology

/-! # Reference Hodge Holomorphic Bundles -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ReferenceHodgeHolomorphicBundles

noncomputable section

section

/-! The original rational Hodge predicate forces the actual exponential obstruction to vanish. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

local instance (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : StronglyLocallyContractibleSpace V.analyticSpace :=
  AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace V.analyticModel V.analyticSpace

theorem originalRationalHodge_holomorphicObstruction_zero (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : V.rationalCohomology 2) (ha : V.IsRationalHodgeClass 1 a) :
    Rational.HolomorphicPeriod.rationalHolomorphicObstruction V.analyticModel V.analyticSpace
      (Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv (TopCat.of V.analyticSpace) 1 a) = 0 := by
  apply Rational.ComplexPeriod.rationalHolomorphicObstruction_zero_of_complex
  obtain ⟨form, hform, hi⟩ := (V.isRationalHodgeClass_iff_integration 1 a).mp ha
  have hc := ConcreteCategory.congr_hom (C := AddCommGrpCat.{0})
    (Rational.BettiComplexSheaf.rationalBettiCechSheafIso_complex V.analyticModel V.analyticSpace 1) a
  change Intrinsic.BettiSheafMaps.nativeSmoothCohomologyToSheaf V.analyticModel V.analyticSpace 1 (V.rationalToSmoothSingular 2 a) =
    CategoryTheory.Sheaf.H.map (Rational.ComplexPeriod.rationalConstantComplexSheafMap (TopCat.of V.analyticSpace)) 2
      (Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv (TopCat.of V.analyticSpace) 1 a) at hc
  rw [← hi, Intrinsic.SmoothIntegration.nativeSmoothCohomologyToSheaf_integration] at hc
  rw [← hc]
  exact IntegratedHodgeSheaf.manifoldIntegratedHodgeClass_holomorphic_zero form hform

theorem originalRationalHodge_holomorphicChern_multiple (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : V.rationalCohomology 2) (ha : V.IsRationalHodgeClass 1 a) :
    ∃ N : ℕ, 0 < N ∧ ∃ u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace,
      Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace u = N • a :=
  Holomorphic.Lifting.exists_holomorphicFirstChernClassQ_multiple V.analyticModel V.analyticSpace a
    (originalRationalHodge_holomorphicObstruction_zero V a ha)

end

/-! Actual holomorphic bundles for original rational Hodge classes and the original projective components. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (a : V.rationalCohomology 2) (ha : V.IsRationalHodgeClass 1 a)

def originalHodgeIntegralMultiple : ℕ := (originalRationalHodge_holomorphicChern_multiple V a ha).choose

theorem originalHodgeIntegralMultiple_pos : 0 < originalHodgeIntegralMultiple V a ha :=
  (originalRationalHodge_holomorphicChern_multiple V a ha).choose_spec.1

def originalHodgeHolomorphicUnitClass : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace :=
  (originalRationalHodge_holomorphicChern_multiple V a ha).choose_spec.2.choose

theorem originalHodgeHolomorphicUnitClass_chern :
    Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace (originalHodgeHolomorphicUnitClass V a ha) =
      originalHodgeIntegralMultiple V a ha • a :=
  (originalRationalHodge_holomorphicChern_multiple V a ha).choose_spec.2.choose_spec

def originalHodgeHolomorphicBundleCore : VectorBundleCore ℂ V.analyticSpace ℂ V.analyticSpace :=
  HolomorphicLine.Bundle.holomorphicLineBundleCore V.analyticModel V.analyticSpace (originalHodgeHolomorphicUnitClass V a ha)

theorem originalHodgeHolomorphicBundle_holomorphic :
    ContMDiffVectorBundle ∞ ℂ (originalHodgeHolomorphicBundleCore V a ha).Fiber 𝓘(ℂ, V.analyticModel) :=
  HolomorphicLine.Bundle.holomorphicLineBundle_contMDiff V.analyticModel V.analyticSpace (originalHodgeHolomorphicUnitClass V a ha)

theorem originalPresentationHodge_componentChern_multiple (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (b : P.rationalCohomology 2) (hb : P.IsRationalHodgeClass 1 b) (C : irreducibleComponents P.carrier) :
    ∃ N : ℕ, 0 < N ∧ ∃ u : Holomorphic.Connecting.holomorphicUnitCohomology (P.componentVariety C).analyticModel (P.componentVariety C).analyticSpace,
      Holomorphic.Singular.holomorphicFirstChernClassQ (P.componentVariety C).analyticModel (P.componentVariety C).analyticSpace u =
        N • (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2 b C) :=
  originalRationalHodge_holomorphicChern_multiple (P.componentVariety C)
    (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2 b C) ((P.isRationalHodgeClass_iff_components 1 b).mp hb C)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ReferenceHodgeHolomorphicBundles
