import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.CutoffNeighborhood
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.Gluing

/-! # Smooth Representative -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.SmoothRepresentative

noncomputable section

/-! The original weak Green solution with original smooth forcing is represented by a genuine original global smooth bundle form. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

theorem holomorphicMetricSmoothGreen_exists_smooth_representative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (hc : h.smoothDolbeaultOneCoercive V) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    ∃ b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1, Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 b = ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a))) :=
  HolomorphicSmooth.Gluing.holomorphic_smooth_representative_of_local_cutoffs V h 1 ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)))
    (fun x => CutoffNeighborhood.holomorphicMetricSmoothGreen_frame_cutoff_neighborhood V h (chartAt V.analyticModel x)
      (chart_mem_atlas V.analyticModel x) x x (mem_chart_source V.analyticModel x)
      ((Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x) hc a)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.SmoothRepresentative
