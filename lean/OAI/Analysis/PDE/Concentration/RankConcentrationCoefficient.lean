import OAI.Analysis.PDE.Concentration.BallDeterminant

noncomputable section
namespace OAI.Analysis.PDE.Concentration

/-- One coefficient, depending only on the dimension, background rank and
its spectral upper bound, works at every positive density and scale. -/
theorem exists_rank_barrier_coefficient (m r : ℕ) (hr : r < m)
    {C₀ : ℝ} (hC : 0 ≤ C₀) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (lam m₀ : ℝ),
      0 < lam → 0 ≤ m₀ → m₀ ≤ lam ^ (m-r) →
      let α := c * m₀ ^ (1 / ((m-r : ℕ) : ℝ))
      α ≤ lam ∧
        (C₀ * lam + 6 * α) ^ r * (6 * α) ^ (m-r) ≤ lam ^ r * m₀ / 2 := by
  let d := m-r
  have hd : d ≠ 0 := by dsimp [d]; omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero hd)
  let D : ℝ := (C₀+6)^r * 6^d
  have hD : 0 < D := by dsimp [D]; positivity
  let c : ℝ := (1 / (2*(D+1))) ^ (1 / (d : ℝ))
  have hden : 0 < 2*(D+1) := by positivity
  have hbase : 0 < 1 / (2*(D+1)) := one_div_pos.mpr hden
  have root_power (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / (d : ℝ))) ^ d = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx,
      div_mul_cancel₀ 1 hdpos.ne', Real.rpow_one]
  have hc : 0 < c := Real.rpow_pos_of_pos hbase _
  have hcpow : c ^ d = 1 / (2*(D+1)) := root_power _ hbase.le
  have hc1 : c ≤ 1 := by
    apply le_of_pow_le_pow_left₀ hd zero_le_one
    rw [hcpow, one_pow]
    exact (div_le_one hden).mpr (by linarith)
  refine ⟨c,hc,hc1,?_⟩
  intro lam m₀ hlam hm₀ hml
  change let α := c*m₀^(1/(d:ℝ)); α ≤ lam ∧
    (C₀*lam+6*α)^r*(6*α)^d ≤ lam^r*m₀/2
  dsimp only
  let α := c*m₀^(1/(d:ℝ))
  have hα : 0 ≤ α := mul_nonneg hc.le (Real.rpow_nonneg hm₀ _)
  have hapow : α ^ d = m₀ / (2*(D+1)) := by
    dsimp only [α]
    rw [mul_pow,hcpow,root_power m₀ hm₀]
    ring
  have ham : α ^ d ≤ m₀ := by
    rw [hapow]
    exact (div_le_iff₀ hden).mpr (by nlinarith)
  have hal : α ≤ lam := le_of_pow_le_pow_left₀ hd hlam.le (ham.trans hml)
  refine ⟨hal,?_⟩
  change (C₀*lam+6*α)^r*(6*α)^d ≤ lam^r*m₀/2
  have hu : C₀*lam+6*α ≤ (C₀+6)*lam := by nlinarith
  have hpow : (C₀*lam+6*α)^r ≤ ((C₀+6)*lam)^r := by gcongr
  calc
    _ ≤ ((C₀+6)*lam)^r*(6*α)^d :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = D*lam^r*α^d := by dsimp only [D]; rw [mul_pow,mul_pow]; ring
    _ ≤ lam^r*m₀/2 := by
      rw [hapow]
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
      have he : (D*lam^r*(m₀/(2*(D+1))))*2 =
          (D/(D+1))*(lam^r*m₀) := by field_simp
      rw [he]
      exact mul_le_of_le_one_left (by positivity)
        ((div_le_one (by positivity : 0<D+1)).mpr (by linarith))

theorem rank_density_root_mul (m r : ℕ) {m₀ : ℝ} (hm₀ : 0 < m₀) :
    m₀ ^ (1 / ((m-r : ℕ) : ℝ)) * m₀ =
      m₀ ^ (1 + 1 / ((m-r : ℕ) : ℝ)) := by
  rw [Real.rpow_add hm₀, Real.rpow_one, mul_comm]

end OAI.Analysis.PDE.Concentration
