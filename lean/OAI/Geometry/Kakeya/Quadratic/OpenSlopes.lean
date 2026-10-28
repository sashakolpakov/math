import OAI.Geometry.Kakeya.Quadratic.OpenDirections
import Mathlib.Analysis.Normed.Module.FiniteDimension

open OAI.Analysis.Fourier.Wave

open Set _root_.MeasureTheory Metric Module
open scoped Topology

noncomputable section
namespace OAI.Geometry.Kakeya.Quadratic

/-- An open ball of graph slopes is sufficient for full Hausdorff
dimension.  The change to unit directions has a uniform positive length. -/
theorem dimH_eq_of_open_slopes (hK : OAI.MeasureTheory.Kakeya.KakeyaConjecture)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (hn : 1 ≤ finrank ℝ F)
    {K : Set (F × ℝ)} {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 < τ)
    (hseg : ∀ a ∈ ball (0 : F) ε, ∃ x : F × ℝ,
      ∀ t ∈ Icc (-τ) τ, x + t • (a, (1 : ℝ)) ∈ K) :
    dimH K = (finrank ℝ F + 1 : ℕ) := by
  let n := finrank ℝ F + 1
  let e : (F × ℝ) ≃L[ℝ] Space n := ContinuousLinearEquiv.ofFinrankEq (by
    simp [Space, n, Module.finrank_prod])
  let U : Set (Space n) := {w | 0 < (e.symm w).2 ∧
    ‖(e.symm w).1‖ < ε * (e.symm w).2}
  have hU : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const (continuous_snd.comp e.symm.continuous)
    · exact isOpen_lt ((continuous_fst.comp e.symm.continuous).norm)
        (continuous_const.mul (continuous_snd.comp e.symm.continuous))
  let v₀ := e (0, (1 : ℝ))
  have hv₀ : v₀ ≠ 0 := by
    intro h
    have := e.injective (h.trans e.map_zero.symm)
    have := congrArg Prod.snd this
    norm_num at this
  have hvnorm : 0 < ‖v₀‖ := norm_pos_iff.mpr hv₀
  let v := ‖v₀‖⁻¹ • v₀
  have hev : e.symm v = (0, ‖v₀‖⁻¹) := by simp [v, v₀]
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hvnorm]
    exact inv_mul_cancel₀ (ne_of_gt hvnorm)
  have hvU : v ∈ U := by
    change 0 < (e.symm v).2 ∧ ‖(e.symm v).1‖ < ε * (e.symm v).2
    rw [hev]
    simpa only [norm_zero] using And.intro (inv_pos.mpr hvnorm) (mul_pos hε (inv_pos.mpr hvnorm))
  let M : ℝ := ‖e.symm.toContinuousLinearMap‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hsmall : 0 < τ / M := div_pos hτ hM
  have hfull : dimH (e '' K) = n := dimH_eq_of_open_directions hK (by dsimp [n]; omega)
    hU hv hvU hsmall (by
      intro ω hω hωnorm
      have hc : 0 < (e.symm ω).2 := hω.1
      let c : ℝ := (e.symm ω).2
      let a : F := c⁻¹ • (e.symm ω).1
      have ha : a ∈ ball (0 : F) ε := by
        rw [mem_ball, dist_zero_right]
        dsimp [a]
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
        have := hω.2
        change ‖(e.symm ω).1‖ < ε * c at this
        calc
          c⁻¹ * ‖(e.symm ω).1‖ < c⁻¹ * (ε * c) := mul_lt_mul_of_pos_left this (inv_pos.mpr hc)
          _ = ε * (c⁻¹ * c) := by ring
          _ = ε := by rw [inv_mul_cancel₀ (show c ≠ 0 from ne_of_gt hc), mul_one]
      have hcM : c ≤ M := by
        calc
          c ≤ |c| := le_abs_self _
          _ ≤ ‖e.symm ω‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le (e.symm ω)
          _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖ω‖ := e.symm.toContinuousLinearMap.le_opNorm ω
          _ ≤ M := by rw [hωnorm, mul_one]; dsimp [M]; linarith
      have hdir : c • (a, (1 : ℝ)) = e.symm ω := by
        apply Prod.ext
        · change c • (c⁻¹ • (e.symm ω).1) = (e.symm ω).1
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul]
        · simp [c]
      obtain ⟨x, hx⟩ := hseg a ha
      refine ⟨e x, ?_⟩
      intro t ht
      have habst : |t| ≤ τ / M := abs_le.mpr ht
      have htc : t*c ∈ Icc (-τ) τ := by
        apply abs_le.mp
        rw [abs_mul, abs_of_pos hc]
        calc
          |t| * c ≤ (τ / M) * c := mul_le_mul_of_nonneg_right habst hc.le
          _ ≤ (τ / M) * M := mul_le_mul_of_nonneg_left hcM hsmall.le
          _ = τ := div_mul_cancel₀ _ (ne_of_gt hM)
      refine ⟨x+(t*c) • (a, (1 : ℝ)), hx _ htc, ?_⟩
      rw [mul_smul, hdir, map_add, map_smul, e.apply_symm_apply])
  simpa only [e.dimH_image] using hfull

end OAI.Geometry.Kakeya.Quadratic
