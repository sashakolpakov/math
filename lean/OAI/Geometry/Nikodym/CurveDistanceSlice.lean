import OAI.Geometry.Nikodym.CompactCurveDistance

open Set Metric
noncomputable section
namespace OAI.Geometry.Nikodym

theorem continuous_infDist_range_parameter
    {P J X : Type*} [TopologicalSpace P] [TopologicalSpace J]
    [CompactSpace J] [Nonempty J] [PseudoMetricSpace X]
    (γ : P × J → X) (hγ : Continuous γ) (x : X) :
    Continuous (fun p => infDist x (range (fun t => γ (p,t)))) := by
  let d : P → J → ℝ := fun p t => dist x (γ (p,t))
  have hd : Continuous (Function.uncurry d) := continuous_const.dist hγ
  have H := isCompact_univ.continuous_sInf (f := d) hd
  simpa only [infDist_range_eq_sInf,d] using H

end OAI.Geometry.Nikodym
