import OAI.Analysis.PDE.Elliptic.Boundary.HolderGluing

/-! Boundary trace, boundary approach, and relative interior Hölder
estimates combine uniformly, with no assumed closed-domain Hölder bound. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Metric

theorem exists_holder_constant_of_boundary_projection
    {X Y : Type*} [MetricSpace X] [NormedAddCommGroup Y]
    {K : Set X} {height : X → ℝ} {proj : X → X}
    {a b c κ A B C V : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hb1 : b < 1) (hc : 0 < c) (hκ : 0 < κ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (hheight : ∀ x ∈ K, 0 ≤ height x ∧ height x ≤ 1)
    (hheight_lip : ∀ x ∈ K, ∀ y ∈ K, height y ≤ height x + dist x y)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ 1) :
    ∃ γ D : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < D ∧ ∀ f : X → Y,
      (∀ x ∈ K, ‖f x‖ ≤ V) →
      (∀ x ∈ K, ‖f x - f (proj x)‖ ≤ A * height x ^ a) →
      (∀ x ∈ K, ∀ y ∈ K, ‖f (proj x) - f (proj y)‖ ≤ C * dist x y ^ c) →
      (∀ x ∈ K, ∀ y ∈ K, 0 < height x → dist x y ≤ κ * height x / 2 →
        ‖f x - f y‖ ≤ B * (dist x y / height x) ^ b) →
      ∀ x ∈ K, ∀ y ∈ K, ‖f x - f y‖ ≤ D * dist x y ^ γ := by
  let a₀ := min a c
  let γ := min a₀ b / 2
  let q := min 1 ((κ / 2) ^ 2)
  let D := (2 * A) * 2 ^ a₀ + C + B + 2 * V / q ^ γ + 1
  have ha₀ : 0 < a₀ := lt_min ha hc
  have hγ : 0 < γ := half_pos (lt_min ha₀ hb)
  have hγ1 : γ < 1 := by
    have ht : min a₀ b ≤ b := min_le_right _ _
    dsimp [γ]
    linarith
  have hq : 0 < q := lt_min zero_lt_one (sq_pos_of_pos (half_pos hκ))
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨γ, D, hγ, hγ1, hD, ?_⟩
  intro f hbound happ htrace hint
  apply holder_of_boundary_and_interior_bound ha₀ hb hκ (by positivity) hB hC hV
    (fun x hx => (hheight x hx).1) hbound _ hint
  intro x hx y hy
  have hd : 0 ≤ dist x y := dist_nonneg
  have hd1 := hdiam x hx y hy
  have hp (z : X) (hz : z ∈ K) : height z ^ a ≤ height z ^ a₀ :=
    Real.rpow_le_rpow_of_exponent_ge' (hheight z hz).1 (hheight z hz).2 ha₀.le (min_le_left _ _)
  have hxpow : height x ^ a₀ ≤ (height x + dist x y) ^ a₀ :=
    Real.rpow_le_rpow (hheight x hx).1 (by linarith) ha₀.le
  have hypow : height y ^ a₀ ≤ (height x + dist x y) ^ a₀ :=
    Real.rpow_le_rpow (hheight y hy).1 (hheight_lip x hx y hy) ha₀.le
  have hd_pow : dist x y ^ c ≤ dist x y ^ a₀ :=
    Real.rpow_le_rpow_of_exponent_ge' hd hd1 ha₀.le (min_le_right _ _)
  have hleft := (happ x hx).trans (mul_le_mul_of_nonneg_left ((hp x hx).trans hxpow) hA)
  have hright := (happ y hy).trans (mul_le_mul_of_nonneg_left ((hp y hy).trans hypow) hA)
  have hmiddle := (htrace x hx y hy).trans (mul_le_mul_of_nonneg_left hd_pow hC)
  have htri : ‖f x - f y‖ ≤ ‖f x - f (proj x)‖ +
      ‖f (proj x) - f (proj y)‖ + ‖f (proj y) - f y‖ := by
    have he : f x - f y = (f x - f (proj x)) +
        (f (proj x) - f (proj y)) + (f (proj y) - f y) := by abel
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  rw [norm_sub_rev (f (proj y)) (f y)] at htri
  linarith

end OAI.Analysis.PDE.Elliptic
