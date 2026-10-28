import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Bounded Quotient -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.BoundedQuotient.Constructions.Removable

noncomputable section

/-!
# Removable singularities of bounded analytic quotients

In one variable, a locally bounded meromorphic function has no poles.
Its canonical meromorphic normalization is therefore holomorphic and agrees
with the original function at every point where it was already analytic.
-/

open Set Filter _root_.Metric _root_.Complex
open scoped _root_.Topology

theorem nonnegative_order_of_bounded {f : ℂ → ℂ} {x : ℂ}
    (hbound : ∃ M : ℝ, ∀ᶠ z in 𝓝[≠] x, ‖f z‖ ≤ M) :
    0 ≤ meromorphicOrderAt f x := by
  by_contra hneg
  have ht : Tendsto (fun z => ‖f z‖) (𝓝[≠] x) atTop :=
    tendsto_norm_atTop_iff_cobounded.mpr
      (tendsto_cobounded_of_meromorphicOrderAt_neg (lt_of_not_ge hneg))
  obtain ⟨M, hM⟩ := hbound
  obtain ⟨z, hzM, hMz⟩ := (hM.and (ht.eventually (eventually_gt_atTop M))).exists
  exact (not_lt_of_ge hzM) hMz

theorem analytic_normalization_of_locally_bounded {f : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U)
    (hbound : ∀ x ∈ U, ∃ M : ℝ, ∀ᶠ z in 𝓝[≠] x, ‖f z‖ ≤ M) :
    AnalyticOnNhd ℂ (toMeromorphicNFOn f U) U := by
  intro x hx
  apply (analyticAt_congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf hx)).mpr
  exact (hf x hx).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp
    (nonnegative_order_of_bounded (hbound x hx))

theorem normalization_eq_at_analytic_point {f : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) {x : ℂ} (hx : x ∈ U) (hfx : AnalyticAt ℂ f x) :
    toMeromorphicNFOn f U x = f x := by
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hf hx,
    toMeromorphicNFAt_eq_self.mpr hfx.meromorphicNFAt]

theorem exists_analytic_quotient_extension {f g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hbound : ∃ M : ℝ, ∀ z ∈ U, g z ≠ 0 → ‖f z / g z‖ ≤ M) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F U ∧ ∀ z ∈ U, g z ≠ 0 → F z = f z / g z := by
  let q : ℂ → ℂ := fun z => f z / g z
  have hq : MeromorphicOn q U := hf.meromorphicOn.fun_div hg.meromorphicOn
  obtain ⟨M, hM⟩ := hbound
  have hqbound (z : ℂ) (hz : z ∈ U) : ‖q z‖ ≤ max 0 M := by
    by_cases hgz : g z = 0
    · simp only [q, hgz, div_zero, norm_zero]
      exact le_max_left _ _
    · exact (hM z hz hgz).trans (le_max_right _ _)
  refine ⟨toMeromorphicNFOn q U, analytic_normalization_of_locally_bounded hq ?_, ?_⟩
  · intro x hx
    refine ⟨max 0 M, ?_⟩
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hx)] with z hz
    exact hqbound z hz
  · intro z hz hgz
    exact normalization_eq_at_analytic_point hq hz ((hf z hz).div (hg z hz) hgz)

theorem quotient_eq_circleIntegral {f g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hbound : ∃ M : ℝ, ∀ z ∈ U, g z ≠ 0 → ‖f z / g z‖ ≤ M)
    {x : ℂ} {R : ℝ} (hR : 0 < R) (hball : closedBall x R ⊆ U)
    (hboundary : ∀ z ∈ sphere x R, g z ≠ 0) (hgx : g x ≠ 0) :
    (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(x, R), (z - x)⁻¹ * (f z / g z)) = f x / g x := by
  obtain ⟨F, hF, hFeq⟩ := exists_analytic_quotient_extension hU hf hg hbound
  have hx : x ∈ U := hball (mem_closedBall_self hR.le)
  have hcircle : (∮ z in C(x, R), (z - x)⁻¹ * (f z / g z)) =
      ∮ z in C(x, R), (z - x)⁻¹ * F z := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    change (z - x)⁻¹ * (f z / g z) = (z - x)⁻¹ * F z
    rw [hFeq z (hball (sphere_subset_closedBall hz)) (hboundary z hz)]
  rw [hcircle, ← hFeq x hx hgx]
  simpa only [smul_eq_mul] using
    (hF.differentiableOn.diffContOnCl_ball hball).two_pi_i_inv_smul_circleIntegral_sub_inv_smul
      (mem_ball_self hR)

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.BoundedQuotient.Constructions.Removable
