import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CovariantAdjointIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CovariantAntiPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.PairSeparation

/-! # Global Covariant Adjoint -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The constructed local Chern adjoint is the existing global Dolbeault adjoint on original antiholomorphic one-forms. -/

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

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.weightedCovariantChartAdjoint_eq_global
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    h.weightedCovariantChartAdjoint V e he i 0 f hf hs b.val =
      Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 0 (fun x => star (f x)) (Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.conjugateFunction_smooth V f hf)
        (h.degreeCodifferential V 0 b.val) := by
  apply h.formIntegralPair_real_separates_left V 0
  intro a
  calc
    _ = (h.formIntegralPair V 1 b.val (h.covariantDerivative ⊤ (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 0 f hf a))).re :=
      (h.weightedCovariantChartAdjoint_pair V e he i f hf hs a b.val).symm
    _ = (h.formIntegralPair V 0 (h.degreeCodifferential V 0 b.val) (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 0 f hf a)).re :=
      congrArg Complex.re (h.covariantDerivative_anti_pair V (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 0 f hf a) b)
    _ = _ := congrArg Complex.re (h.formIntegralPair_smulFunction_move V 0 (h.degreeCodifferential V 0 b.val) a f hf)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.degreeCodifferential_eq_chartFrame
    (b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (x : V.analyticSpace) (hxe : x ∈ e.source)
    (hxi : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :
    (h.degreeCodifferential V 0 b.val).val i ⟨x, trivial, hxi⟩ = h.chartCovariantAdjointFrame V e i 0 b.val x := by
  let W : Opens V.analyticSpace := Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
  obtain ⟨f, hf, hs, hfx⟩ := Analysis.HodgeTheory.Decomposition.AdjointLocality.Constructions.exists_projective_cutoff_at V W.isOpen x (show x ∈ W from ⟨hxe, hxi⟩)
  have heq := h.weightedCovariantChartAdjoint_eq_global V e he i f hf hs b
  have hc := congrArg (fun c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0 => c.val i ⟨x, trivial, hxi⟩) heq
  rw [h.weightedCovariantChartAdjoint_inFrame V e he i 0 f hf hs b.val ⟨x, hxe, hxi⟩,
    Holomorphic.SupportedForms.holomorphicLineSmoothMul_apply, hfx, star_one, one_smul, one_smul] at hc
  exact hc.symm

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.degreeCodifferential_chartCoefficients
    (b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 0 (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i 0 (h.degreeCodifferential V 0 b.val)).extension z =
      h.projectiveCovariantAdjointCoefficients V e i 0
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 1 (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i 1 b.val).extension) z := by
  have hc : Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 0
      (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i 0 (h.degreeCodifferential V 0 b.val)).extension z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 0 (h.chartCovariantAdjointFrame V e i 0 b.val) z := by
    apply Analysis.HodgeTheory.Decomposition.AdjointLocality.Constructions.euclideanChartCoefficients_congr_at V 0 e
    rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply
      (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i 0 (h.degreeCodifferential V 0 b.val)) ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, hz.2⟩,
      Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame_apply,
      h.degreeCodifferential_eq_chartFrame V e he i b (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) (e.map_target hz.1) hz.2]
  exact hc.trans (h.chartCovariantAdjointFrame_coefficients V e he i 0 b.val hz.1)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
