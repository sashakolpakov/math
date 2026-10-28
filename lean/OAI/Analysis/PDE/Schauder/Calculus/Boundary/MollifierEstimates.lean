import OAI.Analysis.PDE.Schauder.Calculus.Boundary.MollifierUnit
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.MollifierScaling

/-! Exponent-preserving estimates for moving-scale smoothing of Hölder data. -/

noncomputable section
open _root_.MeasureTheory Set
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem exists_regularizedTrace_unit_iterated_bound (m : ℕ) :
    ∃ C > 0, ∀ (h : EuclideanSpace ℝ (Fin m) → ℝ), Continuous h →
      ∀ W, 0 ≤ W → (∀ y, ‖y‖ ≤ 3 → |h y| ≤ W) → ∀ n : ℕ, 1 ≤ n → n ≤ 3 →
      ‖iteratedFDeriv ℝ n (fun p : ℝ × EuclideanSpace ℝ (Fin m) => regularizedTrace h p.1 p.2)
        (1, 0)‖ ≤ C * W := by
  obtain ⟨C, hC, hb⟩ := exists_regularizedTrace_unit_three_bound m
  refine ⟨C, hC, ?_⟩
  intro h hh W hW hsup n hn hn3
  obtain ⟨h₁, h₂, h₃⟩ := hb h hh W hW hsup
  interval_cases n
  · simpa only [norm_iteratedFDeriv_one] using h₁
  · rw [show 2 = 1 + 1 by rfl, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
    exact h₂
  · rw [show 3 = 2 + 1 by rfl, ← norm_iteratedFDeriv_fderiv,
      show 2 = 1 + 1 by rfl, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
    exact h₃

theorem exists_regularizedTrace_holder_derivative_bound (m : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    ∃ C > 0, ∀ h : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α,
      ∀ (p : ℝ × EuclideanSpace ℝ (Fin m)), p.1 ≠ 0 → ∀ n : ℕ, 1 ≤ n → n ≤ 3 →
      ‖iteratedFDeriv ℝ n (fun q : ℝ × EuclideanSpace ℝ (Fin m) =>
        regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) q.1 q.2) p‖ ≤
        C * ‖h‖ * |p.1| ^ (α - (n : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := exists_regularizedTrace_unit_iterated_bound m
  refine ⟨C * (3 : ℝ) ^ α, mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro h p hp n hn hn3
  let g := fun y : EuclideanSpace ℝ (Fin m) => OAI.Analysis.Normed.Function.Holder.HolderMap.value h (p.2 + p.1 • y) - OAI.Analysis.Normed.Function.Holder.HolderMap.value h p.2
  have hg : Continuous g := ((OAI.Analysis.Normed.Function.Holder.HolderMap.value h).continuous.comp
    (continuous_const.add (continuous_id.const_smul p.1))).sub continuous_const
  have hsup : ∀ y, ‖y‖ ≤ 3 → |g y| ≤ ‖h‖ * |p.1| ^ α * (3 : ℝ) ^ α := by
    intro y hy
    have ht := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le h (p.2 + p.1 • y) p.2
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at ht
    have hh := Real.rpow_le_rpow (mul_nonneg (abs_nonneg p.1) (norm_nonneg y))
      (mul_le_mul_of_nonneg_left hy (abs_nonneg p.1)) hα
    calc
      |g y| ≤ ‖h‖ * (|p.1| * ‖y‖) ^ α := by simpa only [g, Real.norm_eq_abs] using ht
      _ ≤ ‖h‖ * (|p.1| * 3) ^ α := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
      _ = ‖h‖ * |p.1| ^ α * (3 : ℝ) ^ α := by rw [Real.mul_rpow (abs_nonneg _) (by norm_num)]; ring
  have hunit := hb g hg (‖h‖ * |p.1| ^ α * (3 : ℝ) ^ α) (by positivity) hsup n hn hn3
  rw [show g = (fun y => OAI.Analysis.Normed.Function.Holder.HolderMap.value h (p.2 + p.1 • y) - OAI.Analysis.Normed.Function.Holder.HolderMap.value h p.2) by rfl,
    regularizedTrace_derivative_scaling _ (OAI.Analysis.Normed.Function.Holder.HolderMap.value h).continuous hp p.2 (by omega)] at hunit
  have htp : 0 < |p.1| := abs_pos.mpr hp
  have hpow : |p.1| ^ (α - (n : ℝ)) * |p.1| ^ n = |p.1| ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_add htp]
    congr 1
    ring
  apply (mul_le_mul_iff_right₀ (pow_pos htp n)).mp
  calc
    _ ≤ C * (‖h‖ * |p.1| ^ α * (3 : ℝ) ^ α) := hunit
    _ = |p.1| ^ n * (C * (3 : ℝ) ^ α * ‖h‖ * |p.1| ^ (α - (n : ℝ))) := by
      rw [← hpow]
      ring

end OAI.Analysis.PDE.Schauder
