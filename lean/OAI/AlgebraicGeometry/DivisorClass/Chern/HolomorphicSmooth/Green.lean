import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.EnergyCoercivity
import OAI.AlgebraicGeometry.DivisorClass.Chern.CoerciveHilbertSource

/-! # Green -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.Green

noncomputable section

/-! An actual unshifted weak degree-one solver in the closed smooth energy space, retaining the original Dolbeault and Hilbert-adjoint graphs. -/

open scoped _root_.Manifold
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

def holomorphicMetricSmoothWeakSolution : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h →L[ℂ] Holomorphic.EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h :=
  CoerciveHilbertSource.hilbertSourceUnshifted (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h)

def holomorphicMetricSmoothGreen : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h →L[ℂ] Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h :=
  (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h).comp (holomorphicMetricSmoothWeakSolution V h)

private theorem holomorphicMetricSmoothWeakSolution_variational (hc : h.smoothDolbeaultOneCoercive V)
    (f : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h) (v : Holomorphic.EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h) :
    inner ℂ (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyDerivative V h (holomorphicMetricSmoothWeakSolution V h f).val)
        (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyDerivative V h v.val) +
      inner ℂ (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyAdjointValue V h (holomorphicMetricSmoothWeakSolution V h f).val)
        (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyAdjointValue V h v.val) =
      inner ℂ f (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h v) := by
  have hv := CoerciveHilbertSource.hilbertSourceUnshifted_variational (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h)
    (EnergyCoercivity.holomorphicMetricSmoothEnergySource_opNorm V h hc) f v
  have he := JointClosedGraphEnergy.jointEnergy_inner (h.closedDolbeaultOne V) (h.dolbeaultHilbertAdjoint V) (h.antiOneL2Submodule V).subtypeL (holomorphicMetricSmoothWeakSolution V h f).val v.val
  change inner ℂ (holomorphicMetricSmoothWeakSolution V h f) v =
    inner ℂ (holomorphicMetricSmoothGreen V h f) (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h v) +
      inner ℂ (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyDerivative V h (holomorphicMetricSmoothWeakSolution V h f).val)
        (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyDerivative V h v.val) +
      inner ℂ (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyAdjointValue V h (holomorphicMetricSmoothWeakSolution V h f).val)
        (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyAdjointValue V h v.val) at he
  calc
    _ = (inner ℂ (holomorphicMetricSmoothGreen V h f) (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h v) +
      inner ℂ (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyDerivative V h (holomorphicMetricSmoothWeakSolution V h f).val)
        (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyDerivative V h v.val) +
      inner ℂ (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyAdjointValue V h (holomorphicMetricSmoothWeakSolution V h f).val)
        (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyAdjointValue V h v.val)) -
      inner ℂ (holomorphicMetricSmoothGreen V h f) (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h v) := by abel
    _ = inner ℂ (holomorphicMetricSmoothWeakSolution V h f) v -
        inner ℂ (holomorphicMetricSmoothGreen V h f) (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h v) :=
      congrArg (fun q : ℂ => q - inner ℂ (holomorphicMetricSmoothGreen V h f) (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h v)) he.symm
    _ = _ := hv

/-- The weak Green solution satisfies the original smooth test identity. -/
def HolomorphicSmoothGreenTestIdentity : Prop :=
  ∀ (f : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1),
    inner ℂ (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyDerivative V h (holomorphicMetricSmoothWeakSolution V h f).val)
        (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val) +
      inner ℂ (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyAdjointValue V h (holomorphicMetricSmoothWeakSolution V h f).val)
        (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 (h.degreeCodifferential V 0 a.val)) =
      inner ℂ f (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)

theorem holomorphicMetricSmoothGreen_smooth_test (hc : h.smoothDolbeaultOneCoercive V) :
    HolomorphicSmoothGreenTestIdentity V h := by
  intro f a
  exact holomorphicMetricSmoothWeakSolution_variational V h hc f (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.Green
