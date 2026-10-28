import OAI.AlgebraicGeometry.DivisorClass.Chern.ReferenceHodgeHolomorphicBundles
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration

/-! # Fubini Study Holomorphic -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.FubiniStudyHolomorphic

noncomputable section

/-! The original rational Fubini--Study class supplies an actual holomorphic twisting class. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction

theorem fubiniStudy_isRationalHodgeClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    V.IsRationalHodgeClass 1 (ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ V) := by
  apply (V.isRationalHodgeClass_iff 1 (ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ V)).mpr
  exact ⟨ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClosedForm V,
    (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mp (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm_hasBidegree V),
    ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ_comparison V⟩

theorem negativeFubiniStudy_isRationalHodgeClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    V.IsRationalHodgeClass 1 (-ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ V) := by
  change V.rationalCohomologyInclusion 2 (-ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ V) ∈ V.pureBettiSubspace 1 1
  rw [map_neg]
  exact (V.pureBettiSubspace 1 1).neg_mem (fubiniStudy_isRationalHodgeClass V)

def fubiniStudyTwistMultiplicity (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : ℕ :=
  ReferenceHodgeHolomorphicBundles.originalHodgeIntegralMultiple V (-ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ V) (negativeFubiniStudy_isRationalHodgeClass V)

theorem fubiniStudyTwistMultiplicity_pos (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : 0 < fubiniStudyTwistMultiplicity V :=
  ReferenceHodgeHolomorphicBundles.originalHodgeIntegralMultiple_pos V (-ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ V) (negativeFubiniStudy_isRationalHodgeClass V)

def fubiniStudyTwistUnitClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace :=
  ReferenceHodgeHolomorphicBundles.originalHodgeHolomorphicUnitClass V (-ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ V) (negativeFubiniStudy_isRationalHodgeClass V)

theorem fubiniStudyTwistUnitClass_chern (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace (fubiniStudyTwistUnitClass V) =
      fubiniStudyTwistMultiplicity V • (-ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ V) :=
  ReferenceHodgeHolomorphicBundles.originalHodgeHolomorphicUnitClass_chern V (-ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ V) (negativeFubiniStudy_isRationalHodgeClass V)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.FubiniStudyHolomorphic
