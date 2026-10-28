import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Mollification
import OAI.Analysis.Normed.Function.Holder.Banach

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

def boundaryMollifier (m : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- Smoothing at a signed spatial scale. The formula remains meaningful at
zero, where it equals the original datum exactly. -/
def regularizedTrace {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∫ y, (boundaryMollifier m).normed volume y * h (x - t • y)

theorem integrable_regularizedTrace {m : ℕ}
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : Continuous h)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun y ↦ (boundaryMollifier m).normed volume y * h (x - t • y)) := by
  have hc : Continuous (fun y : EuclideanSpace ℝ (Fin m) ↦ h (x - t • y)) :=
    hh.comp (continuous_const.sub (continuous_id.const_smul t))
  have hρ : Continuous ((boundaryMollifier m).normed volume) :=
    (boundaryMollifier m).continuous_normed
  have hs : HasCompactSupport (fun y ↦ (boundaryMollifier m).normed volume y * h (x - t • y)) := by
    exact ((boundaryMollifier m).hasCompactSupport_normed (μ := volume)).mul_right
  exact (hρ.mul hc).integrable_of_hasCompactSupport hs

@[simp] theorem regularizedTrace_zero {m : ℕ}
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    regularizedTrace h 0 x = h x := by
  simp only [regularizedTrace, zero_smul, sub_zero, integral_mul_const,
    (boundaryMollifier m).integral_normed, one_mul]

theorem norm_regularizedTrace_le {m : ℕ} {α : ℝ}
    (h : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    |regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) t x| ≤ ‖h‖ := by
  have hb : ∀ᵐ y, ‖(boundaryMollifier m).normed volume y *
      OAI.Analysis.Normed.Function.Holder.HolderMap.value h (x - t • y)‖ ≤ (boundaryMollifier m).normed volume y * ‖h‖ := by
    filter_upwards with y
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ((boundaryMollifier m).nonneg_normed y)]
    exact mul_le_mul_of_nonneg_left (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le h _)
      ((boundaryMollifier m).nonneg_normed y)
  have hi := ((boundaryMollifier m).integrable_normed (μ := volume)).mul_const ‖h‖
  simpa only [regularizedTrace, Real.norm_eq_abs, integral_mul_const,
    (boundaryMollifier m).integral_normed, one_mul] using norm_integral_le_of_norm_le hi hb

theorem regularizedTrace_sub {m : ℕ}
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : Continuous h)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    regularizedTrace h t x - h x =
      ∫ y, (boundaryMollifier m).normed volume y * (h (x - t • y) - h x) := by
  have hc : h x = ∫ y, (boundaryMollifier m).normed volume y * h x := by
    rw [integral_mul_const, (boundaryMollifier m).integral_normed, one_mul]
  change (∫ y, (boundaryMollifier m).normed volume y * h (x - t • y)) - h x = _
  conv_lhs => rw [hc]
  rw [← integral_sub (integrable_regularizedTrace h hh t x)
    (((boundaryMollifier m).integrable_normed (μ := volume)).mul_const (h x))]
  apply integral_congr_ae
  filter_upwards with y
  ring

theorem norm_regularizedTrace_sub_le {m : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (h : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    |regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) t x - OAI.Analysis.Normed.Function.Holder.HolderMap.value h x| ≤ ‖h‖ * |t| ^ α := by
  rw [regularizedTrace_sub _ (OAI.Analysis.Normed.Function.Holder.HolderMap.value h).continuous]
  have hb : ∀ᵐ y, ‖(boundaryMollifier m).normed volume y *
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value h (x - t • y) - OAI.Analysis.Normed.Function.Holder.HolderMap.value h x)‖ ≤
      (boundaryMollifier m).normed volume y * (‖h‖ * |t| ^ α) := by
    filter_upwards with y
    by_cases hy : (boundaryMollifier m).normed volume y = 0
    · simp [hy]
    have hymem : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1 := by
      change y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (boundaryMollifier m).rOut
      rw [← (boundaryMollifier m).support_normed_eq (μ := volume)]
      exact hy
    have hynorm : ‖y‖ ≤ 1 := (mem_ball_zero_iff.mp hymem).le
    have hd : ‖x - t • y - x‖ ≤ |t| := by
      have he : x - t • y - x = -(t • y) := by abel
      rw [he, norm_neg, norm_smul, Real.norm_eq_abs]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hynorm (abs_nonneg t)
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ((boundaryMollifier m).nonneg_normed y)]
    apply mul_le_mul_of_nonneg_left _ ((boundaryMollifier m).nonneg_normed y)
    have hh := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le h (x - t • y) x
    rw [dist_eq_norm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hd hα) (norm_nonneg h))
  have hi := ((boundaryMollifier m).integrable_normed (μ := volume)).mul_const (‖h‖ * |t| ^ α)
  simpa only [Real.norm_eq_abs, integral_mul_const,
    (boundaryMollifier m).integral_normed, one_mul] using norm_integral_le_of_norm_le hi hb

end OAI.Analysis.PDE.Schauder
