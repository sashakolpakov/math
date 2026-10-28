import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Connected.Clopen

/-! # Identity Eq -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.IdentityEq.Constructions.Identity

noncomputable section

/-!
# RiemannProjectivity: identity continuation on finite-dimensional holomorphic domains

One-variable identity continuation along short complex lines propagates
an open zero set through a connected open domain. This is used to control
irreducibility of the algebraic closure of a connected analytic image.
-/

open Set Filter _root_.Metric
open scoped _root_.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem interior_zero_closed_within {f : V → ℂ} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : V} (hx : x ∈ U)
    (hc : x ∈ closure (interior {z | f z = 0})) : x ∈ interior {z | f z = 0} := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hc (r / 8) (by positivity)
  have hyx : dist y x < r / 8 := by simpa only [dist_comm] using hxy
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [ball_mem_nhds x (by positivity : 0 < r / 8)] with z hz
  have hzx : dist z x < r / 8 := hz
  let line : ℂ → V := fun c => y + c • (z - y)
  have hline : Differentiable ℂ line :=
    (differentiable_id.smul_const (z - y)).const_add y
  have hlineU : MapsTo line (ball (0 : ℂ) 2) U := by
    intro c hc
    apply hball
    have hc2 : ‖c‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hc
    have hv : ‖z - y‖ < r / 4 := by
      have h := dist_triangle z x y
      rw [dist_comm x y] at h
      rw [dist_eq_norm z y] at h
      linarith
    have hdist : dist (line c) x ≤ ‖c‖ * ‖z - y‖ + dist y x := by
      have h := dist_triangle (line c) y x
      simpa only [line, dist_eq_norm, add_sub_cancel_left, norm_smul] using h
    change dist (line c) x < r
    nlinarith [norm_nonneg c, norm_nonneg (z - y)]
  have hfl : DifferentiableOn ℂ (f ∘ line) (ball (0 : ℂ) 2) :=
    hf.comp hline.differentiableOn hlineU
  have hz0 : ∀ᶠ c : ℂ in 𝓝 0, (f ∘ line) c = 0 := by
    have hy0 : ∀ᶠ w in 𝓝 y, f w = 0 := mem_interior_iff_mem_nhds.mp hy
    have hzero : line 0 = y := by simp [line]
    have hl0 : Tendsto line (𝓝 0) (𝓝 y) := by
      simpa only [ContinuousAt, hzero] using
        (show ContinuousAt line 0 from hline.continuous.continuousAt)
    exact hl0.eventually hy0
  have heq := (hfl.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball (0 : ℂ) 2).isPreconnected (mem_ball_self (by norm_num : (0 : ℝ) < 2))
    (hz0.filter_mono nhdsWithin_le_nhds).frequently
  have h1 := heq (show (1 : ℂ) ∈ ball (0 : ℂ) 2 by norm_num [mem_ball, dist_zero_right])
  simpa only [Function.comp_apply, line, one_smul, add_sub_cancel, Pi.zero_apply] using h1

/-- A holomorphic function with an open zero germ on a connected open
domain vanishes on that entire domain. -/
theorem eq_zero_of_zero_germ {f : V → ℂ} {U : Set V}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hf : DifferentiableOn ℂ f U)
    {x : V} (hx : x ∈ U) (hzero : ∀ᶠ y in 𝓝 x, f y = 0) :
    ∀ y ∈ U, f y = 0 := by
  let G := interior {z | f z = 0}
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  have heq : (Subtype.val ⁻¹' G : Set U) = Subtype.val ⁻¹' closure G := by
    ext y
    exact ⟨fun h => subset_closure h,
      fun h => interior_zero_closed_within hU hf y.property h⟩
  have hcl : IsClopen (Subtype.val ⁻¹' G : Set U) := by
    constructor
    · rw [heq]
      exact isClosed_closure.preimage continuous_subtype_val
    · exact isOpen_interior.preimage continuous_subtype_val
  rcases isClopen_iff.mp hcl with hempty | hfull
  · have hmem : (⟨x, hx⟩ : U) ∈ Subtype.val ⁻¹' G := mem_interior_iff_mem_nhds.mpr hzero
    simp only [hempty, mem_empty_iff_false] at hmem
  · intro y hy
    have hmem : (⟨y, hy⟩ : U) ∈ Subtype.val ⁻¹' G := by rw [hfull]; trivial
    exact interior_subset (s := {z | f z = 0}) (show y ∈ G from hmem)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.IdentityEq.Constructions.Identity
