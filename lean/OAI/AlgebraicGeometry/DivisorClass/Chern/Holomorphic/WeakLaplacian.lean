import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.Green
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LaplacianHilbertPair

/-! # Weak Laplacian -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.WeakLaplacian

noncomputable section

/-! The unshifted weak solution satisfies the distributional equation for the original smooth Laplacian. -/

open scoped _root_.Manifold
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal EnergyContinuousExt.smoothCore_fullNormedSpace EnergyContinuousExt.smoothCore_fullInnerProductSpace
  EnergyContinuousExt.smoothCore_normedSpace EnergyContinuousExt.smoothCore_innerProductSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

private theorem holomorphicMetricSmoothEnergy_laplacian_test
    (v : EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    inner ℂ (EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h v)
        (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V a)) =
      inner ℂ (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyDerivative V h v.val)
        (IntegralPairZero.holomorphicFormL2WithInclusion V h 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val) +
      inner ℂ (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyAdjointValue V h v.val)
        (IntegralPairZero.holomorphicFormL2WithInclusion V h 0 (h.degreeCodifferential V 0 a.val)) := by
  refine (EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion_dense V h).induction_on v ?_ ?_
  · exact isClosed_eq ((EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h).continuous.inner continuous_const)
      (((HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyDerivative V h).continuous.comp continuous_subtype_val).inner continuous_const |>.add
        (((HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyAdjointValue V h).continuous.comp continuous_subtype_val).inner continuous_const))
  · intro b
    exact h.smoothAntiLaplacianOne_hilbert_pair V b a

/-- The Green solution solves the weak equation for the original smooth Laplacian. -/
def HolomorphicSmoothGreenLaplacianTest : Prop :=
  ∀ (f : AntiOneSourcePair.HolomorphicAntiOneL2With V h) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1),
    inner ℂ (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h f)
        (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V a)) =
      inner ℂ f (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)

theorem holomorphicMetricSmoothGreen_laplacian_test (hc : h.smoothDolbeaultOneCoercive V) :
    HolomorphicSmoothGreenLaplacianTest V h := by
  intro f a
  exact
    (holomorphicMetricSmoothEnergy_laplacian_test V h (HolomorphicSmooth.Green.holomorphicMetricSmoothWeakSolution V h f) a).trans
      (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen_smooth_test V h hc f a)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.WeakLaplacian
