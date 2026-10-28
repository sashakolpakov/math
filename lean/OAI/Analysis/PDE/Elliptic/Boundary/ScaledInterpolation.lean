import OAI.Analysis.PDE.Elliptic.Boundary.Interpolation

/-! Boundary-scale interpolation: a first-order boundary expansion and a
scale-invariant interior derivative estimate yield an actual derivative
approach rate. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Metric

theorem fderiv_boundary_decay_of_scaled_holder
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : E → V} {x : E} {h A B a b : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 < a) (hb : 0 < b)
    (hf : ∀ y ∈ closedBall x (h / 2), DifferentiableAt ℝ f y)
    (hval : ∀ y ∈ closedBall x (h / 2), ‖f y‖ ≤ A * h ^ (1 + a))
    (hder : ∀ y ∈ closedBall x (h / 2),
      ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ B * (‖y - x‖ / h) ^ b) :
    ‖fderiv ℝ f x‖ ≤ (4 * A + B) * h ^ (a * b / (1 + b)) := by
  let k := a / (1 + b)
  let γ := a * b / (1 + b)
  have hden : 0 < 1 + b := by linarith
  have hk : 0 < k := div_pos ha hden
  have hkγ : k + γ = a := by dsimp [k, γ]; field_simp
  have hbγ : (1 + k) * b = b + γ := by dsimp [k, γ]; field_simp
  let t := h ^ (1 + k) / 2
  have ht : 0 < t := div_pos (Real.rpow_pos_of_pos hh _) (by norm_num)
  have hth : t ≤ h / 2 := by
    have hp : h ^ (1 + k) ≤ h ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith)
    simpa only [Real.rpow_one] using div_le_div_of_nonneg_right hp (by norm_num : (0 : ℝ) ≤ 2)
  have hsub : closedBall x t ⊆ closedBall x (h / 2) := closedBall_subset_closedBall hth
  have hp := fderiv_norm_le_of_holder_remainder ht
    (show 0 ≤ A * h ^ (1 + a) by positivity)
    (show 0 ≤ B / h ^ b by positivity) hb.le
    (fun y hy => hf y (hsub hy)) (fun y hy => hval y (hsub hy))
    (fun y hy => by
      have hd := hder y (hsub hy)
      rw [Real.div_rpow (norm_nonneg _) hh.le] at hd
      exact hd.trans_eq (by ring))
  have hpower : h ^ (1 + a) = h ^ (1 + k) * h ^ γ := by
    rw [← Real.rpow_add hh]
    congr 1
    linarith [hkγ]
  have hfirst : 2 * (A * h ^ (1 + a)) / t = 4 * A * h ^ γ := by
    rw [hpower]
    dsimp [t]
    field_simp
    ring
  have hsecond : (B / h ^ b) * t ^ b ≤ B * h ^ γ := by
    have htbase : t ≤ h ^ (1 + k) := by
      dsimp [t]
      linarith [Real.rpow_pos_of_pos hh (1 + k)]
    have hpow := Real.rpow_le_rpow ht.le htbase hb.le
    have he : (h ^ (1 + k)) ^ b = h ^ b * h ^ γ := by
      rw [← Real.rpow_mul hh.le, hbγ, Real.rpow_add hh]
    rw [he] at hpow
    calc
      (B / h ^ b) * t ^ b ≤ (B / h ^ b) * (h ^ b * h ^ γ) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = B * h ^ γ := by field_simp
  rw [hfirst] at hp
  dsimp only [γ] at *
  nlinarith

end OAI.Analysis.PDE.Elliptic
