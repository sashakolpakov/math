import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyContinuousExt

/-! # Laplacian Hilbert Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original smooth Laplacian paired in the actual antiholomorphic Hilbert space. -/

open scoped _root_.Manifold
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

def HolomorphicMetric.Data.HolomorphicLineMetricData.smoothAntiLaplacianOne (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 :=
  ⟨h.smoothDolbeaultLaplacianOne V a, h.smoothDolbeaultLaplacianOne_anti V a⟩

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothAntiLaplacianOne_hilbert_pair
    (a b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    inner ℂ (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)
        (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V b)) =
      inner ℂ (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val)
        (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 b).val) +
      inner ℂ (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 (h.degreeCodifferential V 0 a.val))
        (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 (h.degreeCodifferential V 0 b.val)) := by
  have hp := (h.formIntegralPair_conj V 1 a.val (h.smoothDolbeaultLaplacianOne V b)).symm.trans
    ((congrArg (starRingEnd ℂ) (h.smoothDolbeaultLaplacianOne_pair V b a)).trans
      ((map_add (starRingEnd ℂ) _ _).trans
        (congrArg₂ (fun x y : ℂ => x + y)
          (h.formIntegralPair_conj V 0 (h.degreeCodifferential V 0 a.val) (h.degreeCodifferential V 0 b.val))
          (h.formIntegralPair_conj V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 b).val))))
  calc
    _ = h.formIntegralPair V 1 a.val (h.smoothDolbeaultLaplacianOne V b) :=
      Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_inner V h a (h.smoothAntiLaplacianOne V b)
    _ = h.formIntegralPair V 0 (h.degreeCodifferential V 0 a.val) (h.degreeCodifferential V 0 b.val) +
        h.formIntegralPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 b).val := hp
    _ = _ := (add_comm _ _).trans
      (congrArg₂ (fun x y : ℂ => x + y)
        (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_inner V h 2 _ _).symm
        (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_inner V h 0 _ _).symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
