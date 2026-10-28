import OAI.Analysis.PDE.Elliptic.Boundary.ScaledInterpolation

/-! Turning a boundary first-order expansion into a quantitative approach
of the actual gradient, using only an interior derivative Hölder estimate. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Metric InnerProductSpace

theorem fderiv_approaches_boundary_slope
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u : E → ℝ} {v z : E} {h A B a b s : ℝ}
    (hv : ‖v‖ = 1) (hz : inner ℝ v z = 0)
    (hh : 0 < h) (hh1 : h ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 < a) (hb : 0 < b)
    (hu : ∀ y ∈ closedBall (z + h • v) (h / 2), DifferentiableAt ℝ u y)
    (hexp : ∀ y, ‖y - z‖ ≤ 2 * h → 0 ≤ inner ℝ v y →
      |u y - s * inner ℝ v y| ≤ A * h ^ a * inner ℝ v y)
    (hder : ∀ y ∈ closedBall (z + h • v) (h / 2),
      ‖fderiv ℝ u y - fderiv ℝ u (z + h • v)‖ ≤ B * (‖y - (z + h • v)‖ / h) ^ b) :
    ‖fderiv ℝ u (z + h • v) - s • innerSL ℝ v‖ ≤
      (8 * A + B) * h ^ (a * b / (1 + b)) := by
  let x := z + h • v
  let L : E →L[ℝ] ℝ := s • innerSL ℝ v
  let f := fun y => u y - L y
  have hx : x ∈ closedBall x (h / 2) := mem_closedBall_self (by positivity)
  have hfx (y) (hy : y ∈ closedBall x (h / 2)) :
      HasFDerivAt f (fderiv ℝ u y - L) y :=
    (hu y hy).hasFDerivAt.sub L.hasFDerivAt
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hheight : inner ℝ v x = h := by
    dsimp [x]
    rw [inner_add_right, hz, real_inner_smul_right, hvv]
    ring
  have hval (y) (hy : y ∈ closedBall x (h / 2)) :
      ‖f y‖ ≤ (2 * A) * h ^ (1 + a) := by
    have hdist : ‖y - x‖ ≤ h / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hy
    have hheightdiff : |inner ℝ v y - h| ≤ h / 2 := by
      calc
        |inner ℝ v y - h| = |inner ℝ v (y - x)| := by rw [inner_sub_right, hheight]
        _ ≤ h / 2 := (abs_real_inner_le_norm v (y - x)).trans
          (by simpa only [hv, one_mul] using hdist)
    have hypos : 0 ≤ inner ℝ v y := by linarith [(abs_le.mp hheightdiff).1]
    have hyupper : inner ℝ v y ≤ 2 * h := by linarith [(abs_le.mp hheightdiff).2]
    have hxz : ‖x - z‖ = h := by
      dsimp [x]
      rw [add_sub_cancel_left, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos hh]
    have hynorm : ‖y - z‖ ≤ 2 * h := by
      have hn := norm_add_le (y - x) (x - z)
      rw [sub_add_sub_cancel, hxz] at hn
      linarith
    have he := hexp y hynorm hypos
    change |u y - s * inner ℝ v y| ≤ _
    calc
      _ ≤ A * h ^ a * inner ℝ v y := he
      _ ≤ A * h ^ a * (2 * h) := mul_le_mul_of_nonneg_left hyupper (by positivity)
      _ = (2 * A) * h ^ (1 + a) := by rw [Real.rpow_add hh, Real.rpow_one]; ring
  have hp := fderiv_boundary_decay_of_scaled_holder hh hh1 (show 0 ≤ 2 * A by positivity)
    hB ha hb (fun y hy => (hfx y hy).differentiableAt) hval (fun y hy => by
      rw [(hfx y hy).fderiv, (hfx x hx).fderiv]
      simpa only [sub_sub_sub_cancel_right] using hder y hy)
  rw [(hfx x hx).fderiv] at hp
  convert hp using 1 ; ring

end OAI.Analysis.PDE.Elliptic
