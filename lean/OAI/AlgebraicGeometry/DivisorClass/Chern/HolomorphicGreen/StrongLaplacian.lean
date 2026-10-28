import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.SmoothAnti
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LaplacianSymmetry
import OAI.AlgebraicGeometry.DivisorClass.Chern.InnerLinearSeparation

/-! # Strong Laplacian -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.StrongLaplacian

noncomputable section

/-! The constructed global smooth Green representative solves the actual original Laplacian equation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

theorem holomorphicMetricSmoothGreen_representative_solves (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (hc : h.smoothDolbeaultOneCoercive V) (a b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (hb : Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h b = HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)) :
    h.smoothAntiLaplacianOne V b = a :=
  InnerLinearSeparation.inner_linear_separates_left (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h)
    (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_injective V h) (h.smoothAntiLaplacianOne V b) a
    (fun c => Eq.trans (h.smoothAntiLaplacianOne_hilbert_symm V b c)
      (Eq.trans (congrArg (fun v : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h =>
          inner ℂ v (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V c))) hb)
        (Holomorphic.WeakLaplacian.holomorphicMetricSmoothGreen_laplacian_test V h hc (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a) c)))

theorem holomorphicMetricSmoothGreen_exists_strong_solution (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (hc : h.smoothDolbeaultOneCoercive V) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    ∃ b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1, h.smoothAntiLaplacianOne V b = a ∧
      Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h b = HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a) :=
  ⟨(SmoothAnti.holomorphicMetricSmoothGreen_exists_smooth_anti V h hc a).choose,
    holomorphicMetricSmoothGreen_representative_solves V h hc a
      (SmoothAnti.holomorphicMetricSmoothGreen_exists_smooth_anti V h hc a).choose
      (SmoothAnti.holomorphicMetricSmoothGreen_exists_smooth_anti V h hc a).choose_spec,
    (SmoothAnti.holomorphicMetricSmoothGreen_exists_smooth_anti V h hc a).choose_spec⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.StrongLaplacian
