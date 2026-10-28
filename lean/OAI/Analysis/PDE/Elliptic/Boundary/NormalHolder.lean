import OAI.Analysis.PDE.Elliptic.Boundary.CenteredHolder

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

/-- Pairwise Hölder continuity of the actual normal derivative on the flat
boundary, with constants independent of the solution and coefficients. -/
theorem boundary_normal_holder
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∀ m M K : ℝ, m ≤ M → 0 ≤ K →
      ∃ C : ℝ, 0 < C ∧
      ∀ (v : EuclideanSpace ℝ ι), ‖v‖ = 1 →
      ∀ (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (u : EuclideanSpace ℝ ι → ℝ), ContDiff ℝ 2 u →
      (∀ x ∈ closedHalfBall v, m * inner ℝ v x ≤ u x ∧ u x ≤ M * inner ℝ v x) →
      (∀ x ∈ closedHalfBall v, ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w (A x w)) →
      (∀ x ∈ closedHalfBall v, ∀ w, inner ℝ w (A x w) ≤ L * ‖w‖ ^ 2) →
      (∀ x ∈ openHalfBall v, |ellipticTrace A u x| ≤ 2 * K * lam * Fintype.card ι) →
      ∀ z z', ‖z‖ ≤ 1 / 8 → ‖z'‖ ≤ 1 / 8 → inner ℝ v z = 0 → inner ℝ v z' = 0 →
        |fderiv ℝ u z v - fderiv ℝ u z' v| ≤ C * ‖z - z'‖ ^ α := by
  obtain ⟨α, hα, hα1, hholder⟩ := boundary_centered_first_order_holder (ι := ι) hlam hL
  refine ⟨α, hα, hα1, ?_⟩
  intro m M K hmM hK
  obtain ⟨C, hC, hCbound⟩ := hholder m M K hmM hK
  refine ⟨2 * C * (4 : ℝ) ^ α, by positivity, ?_⟩
  intro v hv A u hu hbound hlo hhi hLu z z' hz hz' hvz hvz'
  by_cases he : z = z'
  · subst z'
    simp [Real.zero_rpow hα.ne']
  let d := ‖z - z'‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have hdsmall : d ≤ 1 / 4 := (norm_sub_le z z').trans (by linarith)
  let x := z + d • v
  have hheight : inner ℝ v x = d := by simp [x, inner_add_right, hvz, real_inner_smul_right, hv]
  have hnorm : ‖x - z‖ ≤ (4 * d) / 2 := by
    have heq : x - z = d • v := by dsimp [x]; abel
    rw [heq, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos hd]
    linarith
  have hnorm' : ‖x - z'‖ ≤ (4 * d) / 2 := by
    have heq : x - z' = (z - z') + d • v := by dsimp [x]; abel
    rw [heq]
    have hn := norm_add_le (z - z') (d • v)
    rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos hd] at hn
    dsimp [d] at *
    linarith
  have hfirst := hCbound v hv A u hu hbound hlo hhi hLu z (by linarith) hvz
    (4 * d) (by positivity) (by linarith) x hnorm (by rw [hheight]; exact hd.le)
  have hsecond := hCbound v hv A u hu hbound hlo hhi hLu z' (by linarith) hvz'
    (4 * d) (by positivity) (by linarith) x hnorm' (by rw [hheight]; exact hd.le)
  rw [hheight] at hfirst hsecond
  have htriangle := abs_sub_le (u x - fderiv ℝ u z' v * d) 0 (u x - fderiv ℝ u z v * d)
  have hid : (u x - fderiv ℝ u z' v * d) - (u x - fderiv ℝ u z v * d) =
      (fderiv ℝ u z v - fderiv ℝ u z' v) * d := by ring
  rw [hid, abs_mul, abs_of_pos hd] at htriangle
  simp only [sub_zero, zero_sub, abs_neg] at htriangle
  have hdiv : |fderiv ℝ u z v - fderiv ℝ u z' v| ≤ 2 * C * (4 * d) ^ α := by
    apply (mul_le_mul_iff_left₀ hd).mp
    nlinarith
  calc
    |fderiv ℝ u z v - fderiv ℝ u z' v| ≤ 2 * C * (4 * d) ^ α := hdiv
    _ = (2 * C * (4 : ℝ) ^ α) * ‖z - z'‖ ^ α := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hd.le]
      dsimp [d]
      ring

end OAI.Analysis.PDE.Elliptic
