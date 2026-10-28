import OAI.AlgebraicGeometry.DivisorClass.Chern.BaseCutoffGlobalFunctions
import OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalPairChartIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.VariableMetricIntegral

/-! # Base Cutoff Global -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! The actual fixed base cutoff and cutoff-error integrals have their original global metric-volume expressions. -/

open _root_.MeasureTheory
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.baseSquaredCutoff_global_integral (n : ℕ)
    (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (i : Projective.BasePartition.projectiveBaseFiniteCover V) :
    (∫ z, h.projectiveGlobalPair V (chartAt V.analyticModel i.val) n a c z *
      SquaredRealCutoff.squaredRealCutoff (Projective.BaseChartCutoffs.projectiveBaseChartCutoff V i) z) =
      ∫ x, h.globalFormPair V n a c x * (Projective.BaseSquarePartition.projectiveBaseSquarePartition V i x ^ 2 : ℝ) ∂ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V := by
  have hi := h.projectiveGlobalPair_chart_integral V (chartAt V.analyticModel i.val)
    (chart_mem_atlas V.analyticModel i.val) n a c (fun z => Projective.BaseChartCutoffs.projectiveBaseChartCutoff V i z ^ 2)
    ((Projective.BaseChartCutoffs.projectiveBaseChartCutoff_smooth V i).pow 2)
    ((Projective.BaseChartCutoffs.projectiveBaseChartCutoff_compact V i).comp_left (g := fun r : ℝ => r ^ 2) (by norm_num))
    ((tsupport_comp_subset (g := fun r : ℝ => r ^ 2) (by norm_num) (Projective.BaseChartCutoffs.projectiveBaseChartCutoff V i)).trans
      (Projective.BaseChartCutoffs.projectiveBaseChartCutoff_support V i))
  simpa only [SquaredRealCutoff.squaredRealCutoff, Complex.ofReal_pow, BaseCutoffGlobalFunctions.projectiveBaseSquareChartExtension] using hi

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.baseCutoffError_global_integral (n : ℕ)
    (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (i : Projective.BasePartition.projectiveBaseFiniteCover V) :
    (∫ z, h.projectiveGlobalPair V (chartAt V.analyticModel i.val) n a c z *
      (Projective.CutoffEnergy.projectiveCutoffEnergy V (chartAt V.analyticModel i.val) (Projective.BaseChartCutoffs.projectiveBaseChartCutoff V i) z : ℂ)) =
      ∫ x, h.globalFormPair V n a c x * (BaseCutoffGlobalFunctions.projectiveBaseCutoffGlobalError V i x : ℂ) ∂ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V :=
  h.projectiveGlobalPair_chart_integral V (chartAt V.analyticModel i.val) (chart_mem_atlas V.analyticModel i.val) n a c _
    (Projective.CutoffEnergy.projectiveCutoffEnergy_smooth V _ (chart_mem_atlas V.analyticModel i.val) _
      (Projective.BaseChartCutoffs.projectiveBaseChartCutoff_smooth V i) (Projective.BaseChartCutoffs.projectiveBaseChartCutoff_support V i))
    (Projective.CutoffEnergy.projectiveCutoffEnergy_hasCompactSupport V _ _ (Projective.BaseChartCutoffs.projectiveBaseChartCutoff_compact V i))
    ((Projective.CutoffEnergy.projectiveCutoffEnergy_tsupport V _ _).trans (Projective.BaseChartCutoffs.projectiveBaseChartCutoff_support V i))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_mul_real_integrable (n : ℕ)
    (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ) ∞ f) :
    Integrable (fun x => h.globalFormPair V n a c x * (f x : ℂ)) (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V) := by
  apply integrableOn_univ.mp
  exact ((h.globalFormPair_smooth V n a c).continuous.mul (Complex.continuous_ofReal.comp hf.continuous)).continuousOn.integrableOn_compact isCompact_univ

end

section

/-! Summing the fixed base-chart integrals recovers the original global metric pairing and controls every cutoff error. -/

open _root_.MeasureTheory
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.baseSquaredCutoff_integral_sum (n : ℕ)
    (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    (∑ i, ∫ z, h.projectiveGlobalPair V (chartAt V.analyticModel i.val) n a c z *
      SquaredRealCutoff.squaredRealCutoff (Projective.BaseChartCutoffs.projectiveBaseChartCutoff V i) z) = h.formIntegralPair V n a c := by
  simp_rw [h.baseSquaredCutoff_global_integral V n a c]
  have hi (i : Projective.BasePartition.projectiveBaseFiniteCover V) := h.globalFormPair_mul_real_integrable V n a c
    (fun x => Projective.BaseSquarePartition.projectiveBaseSquarePartition V i x ^ 2) ((Projective.BaseSquarePartition.projectiveBaseSquarePartition_smooth V i).pow 2)
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair
  rw [Projective.MetricAdjoint.projectiveMetricVolume_eq_variety V]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, Projective.BaseSquarePartition.projectiveBaseSquarePartition_sum_sq V x,
    Complex.ofReal_one, mul_one]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.baseCutoffError_integral_sum_bound (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    (∑ i, ∫ z, h.projectiveGlobalPair V (chartAt V.analyticModel i.val) n a a z *
      (Projective.CutoffEnergy.projectiveCutoffEnergy V (chartAt V.analyticModel i.val) (Projective.BaseChartCutoffs.projectiveBaseChartCutoff V i) z : ℂ)).re ≤
      Projective.BaseCutoffBounds.projectiveBaseTotalCutoffErrorBound V * (h.formIntegralPair V n a a).re := by
  let E := fun (i : Projective.BasePartition.projectiveBaseFiniteCover V) x => h.globalFormPair V n a a x * (BaseCutoffGlobalFunctions.projectiveBaseCutoffGlobalError V i x : ℂ)
  have hE (i : Projective.BasePartition.projectiveBaseFiniteCover V) : Integrable (E i) (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V) :=
    h.globalFormPair_mul_real_integrable V n a a (BaseCutoffGlobalFunctions.projectiveBaseCutoffGlobalError V i)
      (BaseCutoffGlobalFunctions.projectiveBaseCutoffGlobalError_smooth V i)
  have hS := integrable_finsetSum Finset.univ (fun i _ => hE i)
  have hP := h.globalFormPair_integrable V n a a
  rw [← Projective.MetricAdjoint.projectiveMetricVolume_eq_variety V] at hP
  have hp (x : V.analyticSpace) : (∑ i, E i x).re ≤
      Projective.BaseCutoffBounds.projectiveBaseTotalCutoffErrorBound V * (h.globalFormPair V n a a x).re := by
    simp only [E, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [← Finset.mul_sum, mul_comm (Projective.BaseCutoffBounds.projectiveBaseTotalCutoffErrorBound V)]
    exact mul_le_mul_of_nonneg_left (BaseCutoffGlobalFunctions.projectiveBaseCutoffGlobalError_sum_bound V x) (h.globalFormPair_nonneg V n a x)
  have hi := integral_mono hS.re (hP.re.const_mul (Projective.BaseCutoffBounds.projectiveBaseTotalCutoffErrorBound V)) hp
  rw [integral_re hS, integral_const_mul, integral_re hP] at hi
  simp_rw [h.baseCutoffError_global_integral V n a a]
  have hsum := integral_finsetSum Finset.univ (fun i _ => hE i)
  change (∑ i, ∫ x, E i x ∂ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V).re ≤ _
  rw [← hsum]
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair
  rw [← Projective.MetricAdjoint.projectiveMetricVolume_eq_variety V]
  exact hi

end

/-! The fixed original base cutoff inequalities imply global smooth degree-one Dolbeault coercivity in the original metric. -/

open _root_.MeasureTheory
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

def HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultOneCoercive : Prop :=
  ∀ a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1,
    (h.formIntegralPair V 1 a.val a.val).re ≤
      (h.formIntegralPair V 1 (h.smoothDolbeaultLaplacianOne V a) a.val).re

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultOneCoercive_of_base_cutoffs
    (hB : ∀ i : Projective.BasePartition.projectiveBaseFiniteCover V,
      h.projectiveBochnerCutoffLowerBound V (chartAt V.analyticModel i.val) (Projective.BaseChartCutoffs.projectiveBaseChartCutoff V i)
        (Projective.BaseCutoffBounds.projectiveBaseTotalCutoffErrorBound V + 1)) : h.smoothDolbeaultOneCoercive V := by
  intro a
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hB i a)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Complex.re_sum] at hsum
  rw [h.baseSquaredCutoff_integral_sum V 1 a.val a.val,
    h.baseSquaredCutoff_integral_sum V 1 (h.smoothDolbeaultLaplacianOne V a) a.val] at hsum
  have hE := h.baseCutoffError_integral_sum_bound V 1 a.val
  nlinarith only [hsum, hE]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultOneCoercive_energy
    (hc : h.smoothDolbeaultOneCoercive V) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    (h.formIntegralPair V 1 a.val a.val).re ≤
      (h.formIntegralPair V 0 (h.degreeCodifferential V 0 a.val) (h.degreeCodifferential V 0 a.val)).re +
        (h.formIntegralPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val).re := by
  have hh := hc a
  rw [h.smoothDolbeaultLaplacianOne_pair V a a, Complex.add_re] at hh
  exact hh

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultOneCoercive_kernel
    (hc : h.smoothDolbeaultOneCoercive V) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (ha : h.smoothDolbeaultLaplacianOne V a = 0) : a = 0 := by
  have hz : h.formIntegralPair V 1 0 a.val = 0 := by
    have hs := h.formIntegralPair_smul_left V 1 a.val a.val (0 : ℂ)
    simpa only [zero_smul, map_zero, zero_mul] using hs
  have hh := hc a
  rw [ha, hz, Complex.zero_re] at hh
  apply Subtype.ext
  exact h.formIntegralPair_definite V 1 a.val (le_antisymm hh (h.formIntegralPair_nonneg V 1 a.val))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultOneCoercive_closed_coclosed
    (hc : h.smoothDolbeaultOneCoercive V) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (h0 : h.degreeCodifferential V 0 a.val = 0) (h1 : HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a = 0) : a = 0 :=
  h.smoothDolbeaultOneCoercive_kernel V hc a (h.smoothDolbeaultLaplacianOne_of_closed_coclosed V a h0 h1)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
