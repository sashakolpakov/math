import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.NormBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Equivalence

/-! # Chart On -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.ChartOn

noncomputable section

/-! The actual compact frame restriction extends continuously from original bundle forms to their Hilbert completion. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace) (n : ℕ)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

def holomorphicLineChartFrameTestLinear : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n →ₗ[ℂ]
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n :=
  (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension f hf.contMDiffOn (fun _ hx => (hs hx).2)).comp
    (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i n)

theorem holomorphicLineChartFrameTestLinear_apply (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    holomorphicLineChartFrameTestLinear V e i n f hf hs a = Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i n f hf hs a := rfl

def holomorphicLineChartFrameSmoothL2 : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n →ₗ[ℂ] Analysis.HodgeTheory.Decomposition.Form.Constructions.ProjectiveL2Forms V n :=
  (Analysis.HodgeTheory.Decomposition.Form.Constructions.smoothToProjectiveL2 V n).comp (holomorphicLineChartFrameTestLinear V e i n f hf hs)

theorem holomorphicLineChartFrameSmoothL2_bound :
    ∃ C : ℝ, ∀ a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n,
      ‖holomorphicLineChartFrameSmoothL2 V e i n f hf hs a‖ ≤ C * ‖Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n a‖ := by
  obtain ⟨C, hC, hb⟩ := h.frameCutoff_integral_bound V e i f hf hs
  refine ⟨Real.sqrt C, fun a => ?_⟩
  have hn : ‖holomorphicLineChartFrameSmoothL2 V e i n f hf hs a‖ ^ 2 =
      (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V n (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i n f hf hs a)
        (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i n f hf hs a)).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact congrArg Complex.re (Analysis.HodgeTheory.Decomposition.Form.Constructions.smoothToProjectiveL2_inner V n _ _)
  exact HolomorphicMetric.Equivalence.nonneg_le_sqrt_mul_of_sq_le (norm_nonneg _) (norm_nonneg _) hC.le
    (hn.trans_le ((hb n a).trans_eq
      (congrArg (fun r : ℝ => C * r) (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_norm_sq V h n a)).symm))

def holomorphicLineChartFrameL2 : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h n →L[ℂ] Analysis.HodgeTheory.Decomposition.Form.Constructions.ProjectiveL2Forms V n :=
  (holomorphicLineChartFrameSmoothL2 V e i n f hf hs).extendOfNorm (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n)

theorem holomorphicLineChartFrameL2_on_smooth (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    holomorphicLineChartFrameL2 V h e i n f hf hs (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n a) =
      Analysis.HodgeTheory.Decomposition.Form.Constructions.smoothToProjectiveL2 V n (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i n f hf hs a) :=
  LinearMap.extendOfNorm_eq (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_dense V h n)
    (holomorphicLineChartFrameSmoothL2_bound V h e i n f hf hs) a

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.ChartOn
