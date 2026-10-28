import OAI.AlgebraicGeometry.Comparison.Betti.CircleIntegralNaturality

/-! # Cauchy Polynomial Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CauchyPolynomialNaturality.Dolbeault

noncomputable section

/-! The actual Cauchy-series polynomials commute with continuous
complex-linear coefficient maps, including evaluation of compact families. -/

open _root_.Metric

variable {F G : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

theorem cauchyPowerSeries_coefficient_map (L : F →L[ℂ] G) {g : ℂ → F} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hg : ContinuousOn g (sphere c r)) (n : ℕ) (w : ℂ) :
    L (cauchyPowerSeries g c r n (fun _ => w)) =
      cauchyPowerSeries (fun z => L (g z)) c r n (fun _ => w) := by
  have hne : ∀ z ∈ sphere c r, z - c ≠ 0 := by
    intro z hz he
    have hzc := sub_eq_zero.mp he
    subst z
    simp only [mem_sphere, dist_self, eq_comm, ne_of_gt hr] at hz
  have hc : ContinuousOn (fun z => (w / (z - c)) ^ n • (z - c)⁻¹ • g z) (sphere c r) :=
    ((continuousOn_const.div (continuousOn_id.sub continuousOn_const) hne).pow n).smul
      (((continuousOn_id.sub continuousOn_const).inv₀ hne).smul hg)
  rw [cauchyPowerSeries_apply, cauchyPowerSeries_apply, map_smul, CircleIntegralNaturality.Dolbeault.circleIntegral_map L (hc.circleIntegrable hr.le)]
  simp only [map_smul]

theorem cauchyPowerSeries_partialSum_map (L : F →L[ℂ] G) {g : ℂ → F} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hg : ContinuousOn g (sphere c r)) (n : ℕ) (w : ℂ) :
    L ((cauchyPowerSeries g c r).partialSum n w) =
      (cauchyPowerSeries (fun z => L (g z)) c r).partialSum n w := by
  unfold FormalMultilinearSeries.partialSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact cauchyPowerSeries_coefficient_map L hr hg k w

end

end OAI.AlgebraicGeometry.Comparison.Betti.CauchyPolynomialNaturality.Dolbeault
