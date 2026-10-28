import OAI.Analysis.PDE.Elliptic.Quadratic
import OAI.Analysis.PDE.Dirichlet.Maximum

/-! Compact-domain comparison for the actual real elliptic trace operator,
used below for quantitative boundary barriers. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem ellipticTrace_nonpos_of_localMax
    (A : E → E →L[ℝ] E) {f : E → ℝ} (hf : ContDiff ℝ 2 f) {x : E}
    (hmax : IsLocalMax f x) (hA : ∀ v : E, 0 ≤ inner ℝ v (A x v)) :
    ellipticTrace A f x ≤ 0 := by
  have hH : (-fderiv ℝ (gradient f) x).toLinearMap.IsPositive := by
    constructor
    · intro v w
      change inner ℝ (-(fderiv ℝ (gradient f) x v)) w = inner ℝ v (-(fderiv ℝ (gradient f) x w))
      rw [inner_neg_left, inner_neg_right]
      exact congrArg (fun t : ℝ => -t) (fderiv_gradient_isSymmetric hf x v w)
    · intro v
      change 0 ≤ inner ℝ (-(fderiv ℝ (gradient f) x v)) v
      rw [inner_neg_left, inner_fderiv_gradient hf]
      exact neg_nonneg.mpr (OAI.Analysis.PDE.Dirichlet.hessian_nonpos_of_localMax hf hmax v)
  have ht := trace_comp_lower_of_positive (A x) (-fderiv ℝ (gradient f) x) hH
    (lam := 0) (fun v => by simpa using hA v)
  simpa only [zero_mul, ContinuousLinearMap.comp_neg, ContinuousLinearMap.toLinearMap_neg,
    map_neg, neg_nonneg, ellipticTrace] using ht

theorem ellipticTrace_strict_maximum
    (A : E → E →L[ℝ] E) {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ}
    (hA : ∀ x ∈ interior K, ∀ v : E, 0 ≤ inner ℝ v (A x v))
    (hL : ∀ x ∈ interior K, 0 < ellipticTrace A f x)
    (hbd : ∀ x ∈ K, x ∉ interior K → f x ≤ M) : ∀ x ∈ K, f x ≤ M := by
  intro x hx
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hf.continuous.continuousOn
  by_cases hyi : y ∈ interior K
  · exact False.elim ((not_lt_of_ge (ellipticTrace_nonpos_of_localMax A hf
      (hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hyi)) (hA y hyi))) (hL y hyi))
  · exact (hmax hx).trans (hbd y hy hyi)

theorem ellipticTrace_maximum
    (A : E → E →L[ℝ] E) {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ}
    (hA : ∀ x ∈ interior K, ∀ v : E, 0 ≤ inner ℝ v (A x v))
    (htrace : ∀ x ∈ interior K, 0 < LinearMap.trace ℝ E (A x).toLinearMap)
    (hL : ∀ x ∈ interior K, 0 ≤ ellipticTrace A f x)
    (hbd : ∀ x ∈ K, x ∉ interior K → f x ≤ M) : ∀ x ∈ K, f x ≤ M := by
  intro x hx
  let b := fun y : E => ‖y‖ ^ 2
  have hb : ContDiff ℝ 2 b := contDiff_norm_sq ℝ
  obtain ⟨z, hz, hbmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hb.continuous.continuousOn
  have hbL (y : E) : ellipticTrace A b y = 2 * LinearMap.trace ℝ E (A y).toLinearMap := by
    simpa only [sub_zero] using ellipticTrace_norm_sq_sub A (0 : E) y
  have hε (ε : ℝ) (hε : 0 < ε) : f x + ε * b x ≤ M + ε * b z := by
    apply ellipticTrace_strict_maximum A hK (hf.add (hb.const_smul ε)) hA _ _ x hx
    · intro y hy
      rw [ellipticTrace_add_smul A hf hb, hbL]
      exact add_pos_of_nonneg_of_pos (hL y hy) (mul_pos hε (mul_pos (by norm_num) (htrace y hy)))
    · intro y hy hyi
      exact add_le_add (hbd y hy hyi) (mul_le_mul_of_nonneg_left (hbmax hy) hε.le)
  have ht : Tendsto (fun ε : ℝ => f x + ε * b x - (M + ε * b z))
      (𝓝[>] 0) (𝓝 (f x - M)) := by
    have hc : Continuous (fun ε : ℝ => f x + ε * b x - (M + ε * b z)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, f x + ε * b x - (M + ε * b z) ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hpos
    exact sub_nonpos.mpr (hε ε hpos)
  exact sub_nonpos.mp (le_of_tendsto ht he)

theorem ellipticTrace_comparison
    (A : E → E →L[ℝ] E) {K : Set E} (hK : IsCompact K)
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hA : ∀ x ∈ interior K, ∀ v : E, 0 ≤ inner ℝ v (A x v))
    (htrace : ∀ x ∈ interior K, 0 < LinearMap.trace ℝ E (A x).toLinearMap)
    (hL : ∀ x ∈ interior K, ellipticTrace A g x ≤ ellipticTrace A f x)
    (hbd : ∀ x ∈ K, x ∉ interior K → f x ≤ g x) : ∀ x ∈ K, f x ≤ g x := by
  have hh := ellipticTrace_maximum A hK (hf.add (hg.const_smul (-1 : ℝ)))
    (M := 0) hA htrace (fun x hx => ?_) (fun x hx hxi => ?_)
  · intro x hx
    simpa only [neg_smul, one_smul, ← sub_eq_add_neg, sub_nonpos] using hh x hx
  · rw [ellipticTrace_add_smul A hf hg]
    linarith [hL x hx]
  · simpa only [neg_smul, one_smul, ← sub_eq_add_neg, sub_nonpos] using hbd x hx hxi

end OAI.Analysis.PDE.Elliptic
