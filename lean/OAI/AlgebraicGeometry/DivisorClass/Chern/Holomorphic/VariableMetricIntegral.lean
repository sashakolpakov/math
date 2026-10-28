import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Data
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormIntegralPair

/-! # Variable Metric Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! Pairing actual bundle-valued forms with any actual smooth Hermitian metric. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

local instance Holomorphic.VariableMetricIntegral.variableMetricPair_finiteDimensional (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℝ V.analyticModel := FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (n : ℕ)

def HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (x : V.analyticSpace) : ℂ :=
  (h.ratio (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u) x : ℂ) * Holomorphic.FormIntegralPair.holomorphicLineGlobalFormPair V u n a b x

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_inFrame (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (i x : V.analyticSpace) (hi : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :
    h.globalFormPair V n a b x = (h.weight i ⟨x, hi⟩ : ℂ) *
      Projective.CovectorPair.projectiveTangentCovectorPair V n x (a.val i ⟨x, trivial, hi⟩) (b.val i ⟨x, trivial, hi⟩) := by
  rw [HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair, Holomorphic.FormIntegralPair.holomorphicLineGlobalFormPair_apply,
    HolomorphicLine.FormPair.holomorphicLineSmoothFormPair_inFrame V u n a b i ⟨x, trivial⟩ hi, ← mul_assoc]
  change ((h.ratio (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u) x : ℂ) *
    ((HolomorphicMetric.Data.holomorphicLineCanonicalMetric u).weight i ⟨x, hi⟩ : ℂ)) * _ = _
  rw [← Complex.ofReal_mul, h.ratio_weight (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u) i ⟨x, hi⟩]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_smooth (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ (h.globalFormPair V n a b) :=
  (contDiff_mul : ContDiff ℝ ∞ (fun p : ℂ × ℂ => p.1 * p.2)).contMDiff.comp
    ((Complex.ofRealCLM.contDiff.contMDiff.comp (h.ratio_smooth (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u))).prodMk_space
      (Holomorphic.FormIntegralPair.holomorphicLineGlobalFormPair_contMDiff V u n a b))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_conj (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (x : V.analyticSpace) : conj (h.globalFormPair V n b a x) = h.globalFormPair V n a b x := by
  simp only [HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair, map_mul, Complex.conj_ofReal,
    Holomorphic.FormIntegralPair.holomorphicLineGlobalFormPair_apply, HolomorphicLine.FormPair.holomorphicLineSmoothFormPair_conj]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_add_left (a b c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (x : V.analyticSpace) : h.globalFormPair V n (a + b) c x =
      h.globalFormPair V n a c x + h.globalFormPair V n b c x := by
  simp only [HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair, Holomorphic.FormIntegralPair.holomorphicLineGlobalFormPair_apply,
    HolomorphicLine.FormPair.holomorphicLineSmoothFormPair_add_left, mul_add]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_smul_left (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (z : ℂ) (x : V.analyticSpace) :
    h.globalFormPair V n (z • a) b x = conj z * h.globalFormPair V n a b x := by
  simp only [HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair, Holomorphic.FormIntegralPair.holomorphicLineGlobalFormPair_apply,
    HolomorphicLine.FormPair.holomorphicLineSmoothFormPair_smul_left]
  ring

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_nonneg (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (x : V.analyticSpace) : 0 ≤ (h.globalFormPair V n a a x).re := by
  change 0 ≤ ((h.ratio (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u) x : ℂ) *
    Holomorphic.FormIntegralPair.holomorphicLineGlobalFormPair V u n a a x).re
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Holomorphic.FormIntegralPair.holomorphicLineGlobalFormPair_apply]
  exact mul_nonneg (h.ratio_positive (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u) x).le
    (HolomorphicLine.FormPair.holomorphicLineSmoothFormPair_nonneg V u n a ⟨x, trivial⟩)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_definite (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (ha : ∀ x, (h.globalFormPair V n a a x).re = 0) : a = 0 := by
  apply HolomorphicLine.FormPair.holomorphicLineSmoothFormPair_definite V u n a
  intro x
  have hx := ha x.val
  change ((h.ratio (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u) x.val : ℂ) *
    Holomorphic.FormIntegralPair.holomorphicLineGlobalFormPair V u n a a x.val).re = 0 at hx
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Holomorphic.FormIntegralPair.holomorphicLineGlobalFormPair_apply] at hx
  exact (mul_eq_zero.mp hx).resolve_left (ne_of_gt (h.ratio_positive (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u) x.val))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_change (k : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (x : V.analyticSpace) :
    h.globalFormPair V n a b x = (h.ratio k x : ℂ) * k.globalFormPair V n a b x := by
  simp only [HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair, ← mul_assoc, ← Complex.ofReal_mul,
    h.ratio_mul k (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u) x]

theorem Holomorphic.VariableMetricIntegral.holomorphicLineCanonicalMetric_globalFormPair (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (x : V.analyticSpace) :
    (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u).globalFormPair V n a b x = Holomorphic.FormIntegralPair.holomorphicLineGlobalFormPair V u n a b x := by
  rw [HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair, HolomorphicMetric.Data.HolomorphicLineMetricData.ratio_self, Complex.ofReal_one, one_mul]

end

section

/-! Genuine metric integrals and positive definite inner products for every constructed Hermitian metric. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (n : ℕ)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_integrable (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    Integrable (h.globalFormPair V n a b) (ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
  apply integrableOn_univ.mp
  exact (h.globalFormPair_smooth V n a b).continuous.continuousOn.integrableOn_compact isCompact_univ

def HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) : ℂ :=
  ∫ x, h.globalFormPair V n a b x ∂(ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair_re (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    (h.formIntegralPair V n a b).re =
      ∫ x, (h.globalFormPair V n a b x).re ∂(ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  (integral_re (h.globalFormPair_integrable V n a b)).symm

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair_conj (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    conj (h.formIntegralPair V n b a) = h.formIntegralPair V n a b := by
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (h.globalFormPair_conj V n a b)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair_add_left (a b c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    h.formIntegralPair V n (a + b) c = h.formIntegralPair V n a c + h.formIntegralPair V n b c := by
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair
  simp_rw [h.globalFormPair_add_left V n a b c]
  exact integral_add (h.globalFormPair_integrable V n a c) (h.globalFormPair_integrable V n b c)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair_smul_left (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (z : ℂ) : h.formIntegralPair V n (z • a) b = conj z * h.formIntegralPair V n a b := by
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair
  simp_rw [h.globalFormPair_smul_left V n a b z]
  exact integral_const_mul (conj z) _

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair_nonneg (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    0 ≤ (h.formIntegralPair V n a a).re := by
  rw [h.formIntegralPair_re]
  exact integral_nonneg (h.globalFormPair_nonneg V n a)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair_definite (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (ha : (h.formIntegralPair V n a a).re = 0) : a = 0 := by
  rw [h.formIntegralPair_re] at ha
  have hae := (integral_eq_zero_iff_of_nonneg (h.globalFormPair_nonneg V n a)
    (h.globalFormPair_integrable V n a a).re).mp ha
  have hc : Continuous (fun x => (h.globalFormPair V n a a x).re) :=
    Complex.continuous_re.comp (h.globalFormPair_smooth V n a a).continuous
  have hz := Measure.eq_of_ae_eq hae hc continuous_const
  exact h.globalFormPair_definite V n a (fun x => congrFun hz x)

@[instance_reducible]
def HolomorphicMetric.Data.HolomorphicLineMetricData.formInnerProductCore : InnerProductSpace.Core ℂ (HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) where
  inner := h.formIntegralPair V n
  conj_inner_symm := h.formIntegralPair_conj V n
  re_inner_nonneg := h.formIntegralPair_nonneg V n
  add_left := h.formIntegralPair_add_left V n
  smul_left := h.formIntegralPair_smul_left V n
  definite a ha := h.formIntegralPair_definite V n a (congrArg Complex.re ha)

theorem Holomorphic.VariableMetricIntegral.holomorphicLineCanonicalMetric_formIntegralPair (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u).formIntegralPair V n a b = Holomorphic.FormIntegralPair.holomorphicLineFormIntegralPair V u n a b := by
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair Holomorphic.FormIntegralPair.holomorphicLineFormIntegralPair
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (Holomorphic.VariableMetricIntegral.holomorphicLineCanonicalMetric_globalFormPair V n a b)

end

/-! Uniform comparison of the actual form integrals for any two smooth positive metrics. -/

open _root_.TopologicalSpace _root_.MeasureTheory Set
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (h k : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.ratio_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ x, h.ratio k x ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.bddAbove_image (h.ratio_smooth k).continuous.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  exact (hC (mem_image_of_mem (h.ratio k) (mem_univ x))).trans (le_max_left _ _)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair_le_of_ratio_le (n : ℕ) (C : ℝ)
    (hC : ∀ x, h.ratio k x ≤ C) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    (h.formIntegralPair V n a a).re ≤ C * (k.formIntegralPair V n a a).re := by
  rw [h.formIntegralPair_re, k.formIntegralPair_re, ← integral_const_mul]
  apply integral_mono (h.globalFormPair_integrable V n a a).re
    ((k.globalFormPair_integrable V n a a).re.const_mul C)
  intro x
  change (h.globalFormPair V n a a x).re ≤ C * (k.globalFormPair V n a a x).re
  rw [h.globalFormPair_change V n k a a x, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_right (hC x) (k.globalFormPair_nonneg V n a x)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n),
      (h.formIntegralPair V n a a).re ≤ C * (k.formIntegralPair V n a a).re := by
  obtain ⟨C, hC, hb⟩ := h.ratio_bounded V k
  exact ⟨C, hC, fun n a => h.formIntegralPair_le_of_ratio_le V k n C hb a⟩

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair_equivalent :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n),
      c * (k.formIntegralPair V n a a).re ≤ (h.formIntegralPair V n a a).re ∧
      (h.formIntegralPair V n a a).re ≤ C * (k.formIntegralPair V n a a).re := by
  obtain ⟨C, hC, hb⟩ := h.formIntegralPair_uniform_bound V k
  obtain ⟨D, hD, hd⟩ := k.formIntegralPair_uniform_bound V h
  refine ⟨D⁻¹, C, inv_pos.mpr hD, hC, ?_⟩
  intro n a
  refine ⟨?_, hb n a⟩
  have hp := mul_le_mul_of_nonneg_left (hd n a) (inv_pos.mpr hD).le
  rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hD), one_mul] at hp

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
