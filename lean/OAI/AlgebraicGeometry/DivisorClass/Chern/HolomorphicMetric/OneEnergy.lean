import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.ClosedSquare
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.HilbertAdjoint
import OAI.AlgebraicGeometry.DivisorClass.Chern.JointClosedGraphEnergy

/-! # One Energy -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.OneEnergy

noncomputable section

/-! The native joint energy of the actual first differential and adjoint for every constructed metric. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (h : Data.HolomorphicLineMetricData u)

def holomorphicMetricOneEnergySubmodule : Submodule ℂ
    (HilbertTripleSq.HilbertTriple (Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h)
      (Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 2) (Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 0)) :=
  JointClosedGraphEnergy.jointEnergySubmodule (h.closedDolbeaultOne V) (h.dolbeaultHilbertAdjoint V) (h.antiOneL2Submodule V).subtypeL

abbrev HolomorphicOneEnergyWith := holomorphicMetricOneEnergySubmodule V h

instance holomorphicMetricOneEnergy_normedAddCommGroup :
    NormedAddCommGroup (HolomorphicOneEnergyWith V h) := inferInstance

instance holomorphicMetricOneEnergy_innerProductSpace :
    InnerProductSpace ℂ (HolomorphicOneEnergyWith V h) :=
  Submodule.innerProductSpace (holomorphicMetricOneEnergySubmodule V h)

instance holomorphicMetricOneEnergy_completeSpace : CompleteSpace (HolomorphicOneEnergyWith V h) :=
  JointClosedGraphEnergy.jointEnergy_completeSpace _ _ _ (h.closedDolbeaultOne_isClosed V) (h.dolbeaultHilbertAdjoint_isClosed V)

def holomorphicMetricOneEnergySource : HolomorphicOneEnergyWith V h →L[ℂ] Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h :=
  JointClosedGraphEnergy.jointEnergySource (h.closedDolbeaultOne V) (h.dolbeaultHilbertAdjoint V) (h.antiOneL2Submodule V).subtypeL

def holomorphicMetricOneEnergyDerivative : HolomorphicOneEnergyWith V h →L[ℂ] Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 2 :=
  JointClosedGraphEnergy.jointEnergyFirstValue (h.closedDolbeaultOne V) (h.dolbeaultHilbertAdjoint V) (h.antiOneL2Submodule V).subtypeL

def holomorphicMetricOneEnergyAdjointValue : HolomorphicOneEnergyWith V h →L[ℂ] Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 0 :=
  JointClosedGraphEnergy.jointEnergySecondValue (h.closedDolbeaultOne V) (h.dolbeaultHilbertAdjoint V) (h.antiOneL2Submodule V).subtypeL

def holomorphicMetricOneSmoothDerivative : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 →ₗ[ℂ] Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 2 :=
  (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 2).comp
    ((HolomorphicLine.AntiForms.holomorphicLineAntiFormSubmodule u ⊤ 2).subtype.comp (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1))

def holomorphicMetricOneSmoothAdjoint : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 →ₗ[ℂ] Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 0 :=
  (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0).comp
    ((h.degreeCodifferential V 0).comp (HolomorphicLine.AntiForms.holomorphicLineAntiFormSubmodule u ⊤ 1).subtype)

private theorem holomorphicMetricOneSmoothAdjoint_graph (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    ((h.antiOneL2Submodule V).subtypeL (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a),
      holomorphicMetricOneSmoothAdjoint V h a) ∈ (h.dolbeaultHilbertAdjoint V).graph := by
  have hx : (h.antiOneL2Submodule V).subtypeL (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a) =
      Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 a.val := by
    change (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a).val = _
    exact Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_val V h a
  have he : ((h.antiOneL2Submodule V).subtypeL (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a),
      holomorphicMetricOneSmoothAdjoint V h a) =
        (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 a.val,
          h.dolbeaultHilbertAdjoint V (h.dolbeaultHilbertAdjointSmoothInclusion V a.val)) :=
    Prod.ext hx (h.dolbeaultHilbertAdjoint_smooth_apply V a.val).symm
  exact Eq.mpr (congrArg (fun z : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1 × Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 0 =>
    z ∈ (h.dolbeaultHilbertAdjoint V).graph) he)
    ((h.dolbeaultHilbertAdjoint V).mem_graph (h.dolbeaultHilbertAdjointSmoothInclusion V a.val))

def holomorphicMetricOneEnergySmoothInclusion :
    HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 →ₗ[ℂ] HolomorphicOneEnergyWith V h :=
  JointClosedGraphEnergy.jointEnergyLift (h.closedDolbeaultOne V) (h.dolbeaultHilbertAdjoint V) (h.antiOneL2Submodule V).subtypeL
    (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h) (holomorphicMetricOneSmoothDerivative V h) (holomorphicMetricOneSmoothAdjoint V h)
    (h.closedDolbeaultOne_smooth_graph V) (holomorphicMetricOneSmoothAdjoint_graph V h)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.OneEnergy
