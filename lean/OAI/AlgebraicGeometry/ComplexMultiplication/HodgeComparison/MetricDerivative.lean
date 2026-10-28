import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential
import OAI.Analysis.HodgeTheory.Decomposition.KahlerMetric

/-! # Metric Derivative -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction

noncomputable section

section

/-! The first derivative of the actual metric is a trilinear tensor with
the differentiated Hermitian symmetry and the closedness identity. -/

open Filter
open scoped _root_.Topology

theorem bilinearDerivative_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E} (hB : DifferentiableAt ℝ B x) (u v w : E) :
    fderiv ℝ (fun y => B y v w) x u = fderiv ℝ B x u v w := by
  rw [fderiv_clm_apply (hB.clm_apply (differentiableAt_const v)) (differentiableAt_const w),
    fderiv_clm_apply hB (differentiableAt_const v)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]

def varietyMetricDerivative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (y : V.analyticModel) :
    V.analyticModel →L[ℝ] V.analyticModel →L[ℝ] V.analyticModel →L[ℝ] ℝ :=
  fderiv ℝ (KahlerDifferential.CM.Construction.varietyMetricInChart V e) y

theorem varietyMetricDerivative_symmetric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {y : V.analyticModel} (hy : y ∈ e.target) (u v w : V.analyticModel) :
    varietyMetricDerivative V e y u v w = varietyMetricDerivative V e y u w v := by
  have hB := ((KahlerDifferential.CM.Construction.varietyMetricInChart_smooth V e he).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  have hEq : (fun z => KahlerDifferential.CM.Construction.varietyMetricInChart V e z v w) =ᶠ[𝓝 y]
      (fun z => KahlerDifferential.CM.Construction.varietyMetricInChart V e z w v) := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact KahlerDifferential.CM.Construction.varietyMetricInChart_symmetric V e he hz v w
  exact (bilinearDerivative_apply _ hB u v w).symm.trans
    ((congrArg (fun L : V.analyticModel →L[ℝ] ℝ => L u) hEq.fderiv_eq).trans
      (bilinearDerivative_apply _ hB u w v))

theorem varietyMetricDerivative_J_skew (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {y : V.analyticModel} (hy : y ∈ e.target) (u v w : V.analyticModel) :
    varietyMetricDerivative V e y u (Complex.I • v) w =
      -varietyMetricDerivative V e y u v (Complex.I • w) := by
  have hB := ((KahlerDifferential.CM.Construction.varietyMetricInChart_smooth V e he).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  have hEq : (fun z => KahlerDifferential.CM.Construction.varietyMetricInChart V e z (Complex.I • v) w) =ᶠ[𝓝 y]
      (fun z => -KahlerDifferential.CM.Construction.varietyMetricInChart V e z v (Complex.I • w)) := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact Analysis.HodgeTheory.Decomposition.KahlerMetric.Constructions.projectiveMetric_J_skew V e he z hz v w
  change fderiv ℝ (KahlerDifferential.CM.Construction.varietyMetricInChart V e) y u (Complex.I • v) w =
    -fderiv ℝ (KahlerDifferential.CM.Construction.varietyMetricInChart V e) y u v (Complex.I • w)
  rw [← bilinearDerivative_apply _ hB, ← bilinearDerivative_apply _ hB, hEq.fderiv_eq,
    fderiv_fun_neg, neg_apply]

theorem varietyMetricDerivative_closed (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {y : V.analyticModel} (hy : y ∈ e.target) (u v w : V.analyticModel) :
    varietyMetricDerivative V e y u v (Complex.I • w) -
      varietyMetricDerivative V e y v u (Complex.I • w) +
      varietyMetricDerivative V e y w u (Complex.I • v) = 0 := by
  have hB := ((KahlerDifferential.CM.Construction.varietyMetricInChart_smooth V e he).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  have h := KahlerDifferential.CM.Construction.varietyMetricInChart_closed_derivative V e he hy u v w
  rw [bilinearDerivative_apply _ hB, bilinearDerivative_apply _ hB, bilinearDerivative_apply _ hB] at h
  exact h

end

section

/-! Closed Hermitian metric derivatives have the holomorphic coefficient
symmetry used in the local Kähler identities. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def hermitianFirstDerivative (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) : ℂ :=
  (T u v w : ℂ) - Complex.I * (T u v (Complex.I • w) : ℂ)

def holomorphicMetricDerivative (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) : ℂ :=
  (1 / 2 : ℂ) * (hermitianFirstDerivative T u v w -
    Complex.I * hermitianFirstDerivative T (Complex.I • u) v w)

omit [IsScalarTower ℝ ℂ E] in
theorem holomorphicMetricDerivative_symmetric
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (hS : ∀ a b c : E, T a b c = T a c b)
    (hJ : ∀ a b c : E, T a (Complex.I • b) c = -T a b (Complex.I • c))
    (hclosed : ∀ a b c : E,
      T a b (Complex.I • c) - T b a (Complex.I • c) + T c a (Complex.I • b) = 0)
    (u v w : E) : holomorphicMetricDerivative T u v w = holomorphicMetricDerivative T w v u := by
  have hJJ (a b c : E) : T a (Complex.I • b) (Complex.I • c) = T a b c := by
    rw [hJ, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg, neg_neg]
  have hR₁ := hclosed u w (Complex.I • v)
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at hR₁
  rw [hS u w v, hS w u v] at hR₁
  have hR₂ := hclosed (Complex.I • u) (Complex.I • w) (Complex.I • v)
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at hR₂
  rw [hS (Complex.I • u) (Complex.I • w) v,
    hS (Complex.I • w) (Complex.I • u) v, hJ (Complex.I • v) u w] at hR₂
  have hR : T u v w - T (Complex.I • u) v (Complex.I • w) =
      T w v u - T (Complex.I • w) v (Complex.I • u) := by linarith
  have hI₁ := hclosed u w v
  rw [hS u w (Complex.I • v), hJ u v w, hS w u (Complex.I • v), hJ w v u] at hI₁
  have hI₂ := hclosed (Complex.I • u) (Complex.I • w) v
  rw [hJJ, hJJ] at hI₂
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at hI₂
  rw [hS (Complex.I • u) w v, hS (Complex.I • w) u v, hJ v u w] at hI₂
  have hI : T u v (Complex.I • w) + T (Complex.I • u) v w =
      T w v (Complex.I • u) + T (Complex.I • w) v u := by linarith
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  apply Complex.ext <;>
    simp only [holomorphicMetricDerivative, hermitianFirstDerivative, hhalf,
      Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
    linarith

theorem varietyMetric_holomorphic_derivative_symmetric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {y : V.analyticModel} (hy : y ∈ e.target) (u v w : V.analyticModel) :
    holomorphicMetricDerivative (varietyMetricDerivative V e y) u v w =
      holomorphicMetricDerivative (varietyMetricDerivative V e y) w v u :=
  holomorphicMetricDerivative_symmetric _ (varietyMetricDerivative_symmetric V e he hy)
    (varietyMetricDerivative_J_skew V e he hy) (varietyMetricDerivative_closed V e he hy) u v w

end

/-! The metric derivative tensor gives the actual holomorphic directional
derivative of the projective Hermitian coefficients. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E]

def holomorphicDirectionalDerivative (f : E → ℂ) (x u : E) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f x u - Complex.I * fderiv ℝ f x (Complex.I • u))

theorem hermitianFirstDerivative_eq_fderiv (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    {x : E} (hB : DifferentiableAt ℝ B x) (u v w : E) :
    hermitianFirstDerivative (fderiv ℝ B x) u v w =
      fderiv ℝ (fun y => Analysis.HodgeTheory.Decomposition.KahlerMetric.Constructions.metricHermitianPair (B y) v w) x u := by
  have h₁ := (hB.clm_apply (differentiableAt_const v)).clm_apply (differentiableAt_const w)
  have h₂ := (hB.clm_apply (differentiableAt_const v)).clm_apply (differentiableAt_const (Complex.I • w))
  have hc₁ := Complex.ofRealCLM.hasFDerivAt.comp x h₁.hasFDerivAt
  have hc₂ := Complex.ofRealCLM.hasFDerivAt.comp x h₂.hasFDerivAt
  have hd := hc₁.sub (hc₂.const_mul Complex.I)
  have hv := congrArg (fun L : E →L[ℝ] ℂ => L u) hd.fderiv
  change fderiv ℝ (fun y => Analysis.HodgeTheory.Decomposition.KahlerMetric.Constructions.metricHermitianPair (B y) v w) x u = _ at hv
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul] at hv
  rw [bilinearDerivative_apply _ hB, bilinearDerivative_apply _ hB] at hv
  exact hv.symm

theorem holomorphicMetricDerivative_eq_directional (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    {x : E} (hB : DifferentiableAt ℝ B x) (u v w : E) :
    holomorphicMetricDerivative (fderiv ℝ B x) u v w =
      holomorphicDirectionalDerivative (fun y => Analysis.HodgeTheory.Decomposition.KahlerMetric.Constructions.metricHermitianPair (B y) v w) x u := by
  rw [holomorphicMetricDerivative, hermitianFirstDerivative_eq_fderiv B hB,
    hermitianFirstDerivative_eq_fderiv B hB]
  rfl

theorem varietyHermitian_holomorphic_derivative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {y : V.analyticModel} (hy : y ∈ e.target) (u v w : V.analyticModel) :
    holomorphicDirectionalDerivative
      (fun z => Analysis.HodgeTheory.Decomposition.KahlerMetric.Constructions.metricHermitianPair (KahlerDifferential.CM.Construction.varietyMetricInChart V e z) v w) y u =
    holomorphicDirectionalDerivative
      (fun z => Analysis.HodgeTheory.Decomposition.KahlerMetric.Constructions.metricHermitianPair (KahlerDifferential.CM.Construction.varietyMetricInChart V e z) v u) y w := by
  have hB := ((KahlerDifferential.CM.Construction.varietyMetricInChart_smooth V e he).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  rw [← holomorphicMetricDerivative_eq_directional _ hB, ← holomorphicMetricDerivative_eq_directional _ hB]
  exact varietyMetric_holomorphic_derivative_symmetric V e he hy u v w

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction
