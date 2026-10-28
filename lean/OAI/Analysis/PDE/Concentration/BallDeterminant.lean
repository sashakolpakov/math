import OAI.Analysis.PDE.Concentration.BarrierDeterminant

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Matrix OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

theorem rank_one_quadratic_determinant_upper (n : ℕ)
    (v : Fin (n + 2) → Quaternion ℝ) {α lam C : ℝ}
    (hα : 0 ≤ α) (hal : α ≤ lam)
    (htrace : (∑ i, (OAI.Analysis.Calculus.Quaternion.outer v i i).re) ≤ C) :
    OAI.LinearAlgebra.Moore.mooreDet (n + 2) (lam • OAI.Analysis.Calculus.Quaternion.outer v + (6 * α) • 1) ≤
      (6 ^ (n + 2) + 6 ^ (n + 1) * C) * lam * α ^ (n + 1) := by
  rw [add_comm (lam • OAI.Analysis.Calculus.Quaternion.outer v), mooreDet_scalar_identity_add_outer]
  have hlam : 0 ≤ lam := hα.trans hal
  have htr := mul_le_mul_of_nonneg_left htrace
    (show 0 ≤ lam * (6 * α) ^ (n + 1) by positivity)
  have hp := mul_le_mul_of_nonneg_right hal
    (show 0 ≤ (6 : ℝ) ^ (n + 2) * α ^ (n + 1) by positivity)
  rw [mul_pow, mul_pow, pow_succ α (n + 1)]
  simp only [mul_pow] at htr
  nlinarith

/-- A fixed coefficient makes the quadratic test determinant less than half
the PDE determinant. This is uniform in the lower density and large
background parameter, not a compactness assertion depending on them. -/
theorem exists_quadratic_barrier_coefficient (n : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (lam m : ℝ), 0 < lam → 0 ≤ m → m ≤ lam ^ (n + 1) →
      let α := c * m ^ (1 / ((n : ℝ) + 1))
      α ≤ lam ∧ ∀ v : Fin (n + 2) → Quaternion ℝ,
        (∑ i, (OAI.Analysis.Calculus.Quaternion.outer v i i).re) ≤ C →
        OAI.LinearAlgebra.Moore.mooreDet (n + 2) (lam • OAI.Analysis.Calculus.Quaternion.outer v + (6 * α) • 1) ≤ lam * m / 2 := by
  let D : ℝ := 6 ^ (n + 2) + 6 ^ (n + 1) * C
  have hD : 0 < D := add_pos_of_pos_of_nonneg (by positivity) (by positivity)
  let c : ℝ := (1 / (2 * (D + 1))) ^ (1 / ((n : ℝ) + 1))
  have hden : 0 < 2 * (D + 1) := by positivity
  have hbase : 0 < 1 / (2 * (D + 1)) := one_div_pos.mpr hden
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have root_power (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / ((n : ℝ) + 1))) ^ (n + 1) = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [div_mul_cancel₀ 1 hn.ne', Real.rpow_one]
  have hcpos : 0 < c := Real.rpow_pos_of_pos hbase _
  have hcpow : c ^ (n + 1) = 1 / (2 * (D + 1)) := root_power _ hbase.le
  have hc1 : c ≤ 1 := by
    apply le_of_pow_le_pow_left₀ (by omega : n + 1 ≠ 0) zero_le_one
    rw [hcpow, one_pow]
    exact (div_le_one hden).mpr (by linarith)
  refine ⟨c, hcpos, hc1, ?_⟩
  intro lam m hlam hm hml
  dsimp only
  let α := c * m ^ (1 / ((n : ℝ) + 1))
  have hα : 0 ≤ α := mul_nonneg hcpos.le (Real.rpow_nonneg hm _)
  have hapow : α ^ (n + 1) = m / (2 * (D + 1)) := by
    dsimp only [α]
    rw [mul_pow, hcpow, root_power m hm]
    ring
  have ham : α ^ (n + 1) ≤ m := by
    rw [hapow]
    exact (div_le_iff₀ hden).mpr (by nlinarith)
  have hal : α ≤ lam := le_of_pow_le_pow_left₀ (by omega : n + 1 ≠ 0) hlam.le (ham.trans hml)
  refine ⟨hal, ?_⟩
  intro v hv
  apply (rank_one_quadratic_determinant_upper n v hα hal hv).trans
  change D * lam * α ^ (n + 1) ≤ lam * m / 2
  rw [hapow]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have he : (D * lam * (m / (2 * (D + 1)))) * 2 =
      (D / (D + 1)) * (lam * m) := by field_simp
  rw [he]
  exact mul_le_of_le_one_left (mul_nonneg hlam.le hm)
    ((div_le_one (by positivity : 0 < D + 1)).mpr (by linarith))

end OAI.Analysis.PDE.Concentration
