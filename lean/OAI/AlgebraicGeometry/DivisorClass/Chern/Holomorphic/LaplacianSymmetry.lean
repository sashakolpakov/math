import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LaplacianHilbertPair

/-! # Laplacian Symmetry -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original smooth antiholomorphic Laplacian is symmetric in the original complex Hilbert pairing. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothAntiLaplacianOne_hilbert_symm (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (a b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    inner ℂ (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V a)) (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h b) =
      inner ℂ (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a) (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V b)) :=
  Eq.trans (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_inner V h (h.smoothAntiLaplacianOne V a) b)
    (Eq.trans (h.smoothDolbeaultLaplacianOne_pair V a b)
      (Eq.trans (add_comm _ _)
        (Eq.trans (congrArg₂ (fun x y : ℂ => x + y)
          (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_inner V h 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val
            (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 b).val).symm
          (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_inner V h 0 (h.degreeCodifferential V 0 a.val)
            (h.degreeCodifferential V 0 b.val)).symm)
          (h.smoothAntiLaplacianOne_hilbert_pair V a b).symm)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
