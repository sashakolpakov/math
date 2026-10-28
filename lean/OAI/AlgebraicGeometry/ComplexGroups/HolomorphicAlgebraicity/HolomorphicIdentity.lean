import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness

/-! # Holomorphic Identity -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicIdentity.Constructions.Identity

noncomputable section

/-!
# Local identity principles for finite-dimensional holomorphic equations

Restriction to complex lines proves the identity principle on balls without
assuming a multivariable power-series expansion. This also shows that a
product of holomorphic germs can vanish only if one factor vanishes.
-/

open Set Filter _root_.Metric _root_.Complex
open scoped _root_.Topology

theorem eqOn_zero_ball_of_eventually_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {x : E} {R : ℝ} (hf : DifferentiableOn ℂ f (ball x R))
    (hzero : ∀ᶠ z in 𝓝 x, f z = 0) : EqOn f 0 (ball x R) := by
  intro y hy
  by_cases hyx : y = x
  · simpa only [hyx, Pi.zero_apply] using hzero.self_of_nhds
  let v := y - x
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  have hvr : ‖v‖ < R := mem_ball_iff_norm.mp hy
  let r := R / ‖v‖
  have h1r : 1 < r := (lt_div_iff₀ hv).mpr (by simpa only [one_mul] using hvr)
  have hr : 0 < r := zero_lt_one.trans h1r
  let line : ℂ → E := fun z => x + z • v
  have hline : Differentiable ℂ line := (differentiable_const x).add (differentiable_id.smul_const v)
  have hmaps : MapsTo line (ball (0 : ℂ) r) (ball x R) := by
    intro z hz
    rw [mem_ball_iff_norm]
    change ‖x + z • v - x‖ < R
    rw [add_sub_cancel_left, norm_smul]
    calc
      ‖z‖ * ‖v‖ < r * ‖v‖ := mul_lt_mul_of_pos_right (by simpa only [mem_ball_iff_norm, sub_zero] using hz) hv
      _ = R := div_mul_cancel₀ _ hv.ne'
  have hg := hf.comp hline.differentiableOn hmaps
  have hline0 : Tendsto line (𝓝 0) (𝓝 x) := by
    simpa only [line, zero_smul, add_zero] using hline.continuous.tendsto (0 : ℂ)
  have hgzero : (fun z => f (line z)) =ᶠ[𝓝 (0 : ℂ)] 0 := hline0.eventually hzero
  have hident := (hg.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) r).isPreconnected (mem_ball_self hr) hgzero
  have h := hident (show (1 : ℂ) ∈ ball 0 r by simpa using h1r)
  simpa only [Function.comp_def, line, v, one_smul, ← add_sub_assoc, add_sub_cancel_left,
    Pi.zero_apply] using h

theorem eventually_zero_or_eventually_zero_of_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → ℂ} {U : Set E} {x : E} (hU : IsOpen U) (hx : x ∈ U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hprod : ∀ z ∈ U, f z * g z = 0) :
    (∀ᶠ z in 𝓝 x, f z = 0) ∨ (∀ᶠ z in 𝓝 x, g z = 0) := by
  by_cases hfzero : ∀ᶠ z in 𝓝 x, f z = 0
  · exact Or.inl hfzero
  right
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hsmall : ball x (R / 4) ∈ 𝓝 x := ball_mem_nhds x (by linarith)
  obtain ⟨y, hyf, hy⟩ := ((not_eventually.mp hfzero).and_eventually hsmall).exists
  have hyU : y ∈ U := hball (ball_subset_ball (by linarith) hy)
  have hgy : ∀ᶠ z in 𝓝 y, g z = 0 := by
    filter_upwards [hU.mem_nhds hyU,
      (hf.differentiableAt (hU.mem_nhds hyU)).continuousAt.eventually_ne hyf] with z hz hzf
    exact (mul_eq_zero.mp (hprod z hz)).resolve_left hzf
  have hsub : ball y (R / 2) ⊆ U := by
    apply Subset.trans (ball_subset_ball' (show R / 2 + dist y x ≤ R from by
      have hdist := mem_ball.mp hy
      linarith)) hball
  have hident := eqOn_zero_ball_of_eventually_zero (hg.mono hsub) hgy
  have hxy : x ∈ ball y (R / 2) := by
    rw [mem_ball, dist_comm]
    have hdist := mem_ball.mp hy
    linarith
  filter_upwards [isOpen_ball.mem_nhds hxy] with z hz
  exact hident hz

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicIdentity.Constructions.Identity
