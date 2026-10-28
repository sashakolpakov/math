import OAI.Analysis.Calculus.Coefficients.Potential
import OAI.Analysis.Normed.Function.Holder.Banach.Composition

open Set Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Calculus.Coefficients

variable {X F G : Type*} [MetricSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Smooth coefficient maps preserve uniform convergence and uniform Hölder
bounds on a bounded family of jets. -/
theorem smooth_composition_uniform_holder
    (Φ : F → G) (hΦ : ContDiff ℝ 1 Φ)
    (u : ℕ → X → F) (f : X → F) {K : Set X}
    (hc : TendstoUniformlyOn u f atTop K)
    {R H α : ℝ} (_ : 0 ≤ R) (hH : 0 ≤ H)
    (hu : ∀ j x, x ∈ K → ‖u j x‖ ≤ R)
    (hf : ∀ x, x ∈ K → ‖f x‖ ≤ R)
    (hh : ∀ j x, x ∈ K → ∀ y, y ∈ K →
      ‖u j x-u j y‖ ≤ H*dist x y^α) :
    TendstoUniformlyOn (fun j x ↦ Φ (u j x)) (fun x ↦ Φ (f x)) atTop K ∧
    ∃ C : ℝ, 0 < C ∧
      (∀ j x, x ∈ K → ‖Φ (u j x)‖ ≤ C) ∧
      (∀ j x, x ∈ K → ∀ y, y ∈ K →
        ‖Φ (u j x)-Φ (u j y)‖ ≤ C*dist x y^α) := by
  obtain ⟨L,hL⟩ := hΦ.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : F) R) (isCompact_closedBall (0 : F) R)
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : F) R).exists_bound_of_continuousOn
    hΦ.continuous.continuousOn
  have hu' j x (hx : x ∈ K) : u j x ∈ closedBall (0 : F) R := by
    simpa only [mem_closedBall,dist_zero_right] using hu j x hx
  have hf' x (hx : x ∈ K) : f x ∈ closedBall (0 : F) R := by
    simpa only [mem_closedBall,dist_zero_right] using hf x hx
  constructor
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have hLp : 0 < (L : ℝ)+1 := by positivity
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hc
      (ε/((L : ℝ)+1)) (div_pos hε hLp)] with j hj
    intro x hx
    have h := hL.dist_le_mul _ (hf' x hx) _ (hu' j x hx)
    have hbound : (L : ℝ)*dist (f x) (u j x) < ε := by
      calc
        (L : ℝ)*dist (f x) (u j x) ≤ ((L : ℝ)+1)*dist (f x) (u j x) :=
          mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
        _ < ((L : ℝ)+1)*(ε/((L : ℝ)+1)) :=
          mul_lt_mul_of_pos_left (hj x hx) hLp
        _ = ε := mul_div_cancel₀ ε (ne_of_gt hLp)
    exact h.trans_lt hbound
  · refine ⟨max M 0+(L : ℝ)*H+1,by positivity,?_,?_⟩
    · intro j x hx
      exact (hM _ (hu' j x hx)).trans (by nlinarith [le_max_left M 0,L.coe_nonneg])
    · intro j x hx y hy
      have h := hL.dist_le_mul _ (hu' j x hx) _ (hu' j y hy)
      rw [dist_eq_norm,dist_eq_norm] at h
      refine h.trans ((mul_le_mul_of_nonneg_left (hh j x hx y hy) L.coe_nonneg).trans ?_)
      have hLH : (L : ℝ)*H ≤ max M 0+(L : ℝ)*H+1 := by nlinarith [le_max_right M 0]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hLH (Real.rpow_nonneg dist_nonneg α)

end OAI.Analysis.Calculus.Coefficients
