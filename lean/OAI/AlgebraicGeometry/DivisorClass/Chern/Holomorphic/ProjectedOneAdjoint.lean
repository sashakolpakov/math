import OAI.AlgebraicGeometry.DivisorClass.Chern.CovariantOneDolbeaultPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiMultiplication
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.GlobalCovariantAdjoint

/-! # Projected One Adjoint -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The supported native degree-one adjoint agrees with the projection of the original global Dolbeault adjoint. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.weightedCovariantAdjointOne_projected_eq_global
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 2) :
    Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I (h.weightedCovariantChartAdjoint V e he i 1 f hf hs b.val) =
      Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 (fun x => star (f x)) (Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.conjugateFunction_smooth V f hf)
        (Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I (h.degreeCodifferential V 1 b.val)) := by
  apply h.formIntegralPair_real_separates_left V 1
  intro a
  let pa : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 := Holomorphic.OneFormProjection.holomorphicLineOneAntiProjection u ⊤ a
  let fa : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 :=
    ⟨Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 f hf pa.val, Holomorphic.AntiMultiplication.holomorphicLineSmoothMul_anti u ⊤ f hf 1 pa⟩
  calc
    _ = (h.formIntegralPair V 1 (h.weightedCovariantChartAdjoint V e he i 1 f hf hs b.val) pa.val).re :=
      congrArg Complex.re (h.onePart_integral_pair V _ a)
    _ = (h.formIntegralPair V 2 b.val (h.covariantDerivativeOne ⊤ fa.val)).re :=
      (h.weightedCovariantChartAdjointOne_pair V e he i f hf hs pa.val b.val).symm
    _ = (h.formIntegralPair V 1 (h.degreeCodifferential V 1 b.val) fa.val).re :=
      congrArg Complex.re (h.covariantDerivativeOne_dolbeault_pair V fa b)
    _ = (h.formIntegralPair V 1
        (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 (fun x => star (f x)) (Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.conjugateFunction_smooth V f hf)
          (h.degreeCodifferential V 1 b.val)) pa.val).re :=
      congrArg Complex.re (h.formIntegralPair_smulFunction_move V 1 (h.degreeCodifferential V 1 b.val) pa.val f hf)
    _ = (h.formIntegralPair V 1
        (Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I
          (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 (fun x => star (f x)) (Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.conjugateFunction_smooth V f hf)
            (h.degreeCodifferential V 1 b.val))) a).re :=
      congrArg Complex.re (h.onePart_integral_pair V _ a).symm
    _ = _ := by
      rw [Holomorphic.AntiMultiplication.holomorphicLineOnePart_smoothMul]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
