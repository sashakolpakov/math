import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricBounds
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.NhdsWithin

/-! # Rational Positive Approximation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalPositiveApproximation.CM.Construction

noncomputable section

/-! Strict positivity in a continuous family of finite-dimensional
bilinear forms persists under rational approximation of real parameters. -/

open Set Filter
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {Z : Type*} [TopologicalSpace Z]

theorem positive_bilinear_eventually (B : Z → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : Continuous B) {x : Z} (hx : ∀ u : E, u ≠ 0 → 0 < B x u u) :
    ∀ᶠ y in 𝓝 x, ∀ u : E, u ≠ 0 → 0 < B y u u := by
  have hdiag : Continuous (fun p : Z × E => B p.1 p.2 p.2) :=
    ((hB.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  have hs : ∀ᶠ y in 𝓝 x, ∀ u ∈ Metric.sphere (0 : E) 1, 0 < B y u u := by
    apply (isCompact_sphere (0 : E) 1).eventually_forall_of_forall_eventually
    intro u hu
    have hne : u ≠ 0 := by
      intro hz
      have hn : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu
      rw [hz, norm_zero] at hn
      exact zero_ne_one hn
    exact hdiag.continuousAt.eventually (Ioi_mem_nhds (hx u hne))
  filter_upwards [hs] with y hy
  intro u hu
  let v := (‖u‖⁻¹ : ℝ) • u
  have hv : v ∈ Metric.sphere (0 : E) 1 := by
    simpa [v, Metric.mem_sphere] using norm_smul_inv_norm (𝕜 := ℝ) hu
  have hn : ‖u‖ • v = u := by
    change ‖u‖ • ((‖u‖⁻¹ : ℝ) • u) = u
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu), one_smul]
  have hscale : B y u u = ‖u‖ * ‖u‖ * B y v v := by
    calc
      B y u u = B y (‖u‖ • v) (‖u‖ • v) := by rw [hn]
      _ = _ := by simp only [map_smul, smul_apply, smul_eq_mul]; ring
  rw [hscale]
  exact mul_pos (mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hu)) (hy v hv)

theorem exists_rational_positive_parameters {ι : Type*}
    (B : (ι → ℝ) → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (x : ι → ℝ) (hx : ∀ u : E, u ≠ 0 → 0 < B x u u) :
    ∃ q : ι → ℚ, ∀ u : E, u ≠ 0 → 0 < B (fun i => (q i : ℝ)) u u := by
  have hdense : DenseRange (fun q : ι → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ : ι => (Rat.denseRange_cast : DenseRange (fun q : ℚ => (q : ℝ))))
  exact hdense.mem_nhds (positive_bilinear_eventually B hB hx)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalPositiveApproximation.CM.Construction
