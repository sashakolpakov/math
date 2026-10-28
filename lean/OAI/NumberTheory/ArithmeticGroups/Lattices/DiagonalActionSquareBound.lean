import OAI.NumberTheory.ArithmeticGroups.Lattices.ShortestVector

/-! # Diagonal Action Square Bound -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalActionSquareBound.Construction

noncomputable section

section

/-! A lower gap for nonzero coordinates converts a bound after one
diagonal weighting into a bound after its square. -/

theorem diagonal_weight_square_bound (a w ε R : ℝ) (hε : 0 < ε) (hR : 0 ≤ R)
    (hw : w = 0 ∨ ε ≤ |w|) (hbound : |a * w| ≤ R) : |a ^ 2 * w| ≤ R ^ 2 / ε := by
  rcases hw with rfl | hw
  · simp only [mul_zero, abs_zero]
    exact div_nonneg (sq_nonneg R) hε.le
  · apply (le_div_iff₀ hε).mpr
    calc
      |a ^ 2 * w| * ε ≤ |a ^ 2 * w| * |w| := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
      _ = |a * w| ^ 2 := by rw [abs_mul, abs_pow, abs_mul]; ring
      _ ≤ R ^ 2 := (sq_le_sq₀ (abs_nonneg _) hR).mpr hbound

theorem diagonal_weight_square_pi_bound
    {ι : Type*} [Fintype ι] (a w : ι → ℝ) (ε R : ℝ) (hε : 0 < ε) (hR : 0 ≤ R)
    (hw : ∀ i, w i = 0 ∨ ε ≤ |w i|) (hbound : ‖fun i => a i * w i‖ ≤ R) :
    ‖fun i => a i ^ 2 * w i‖ ≤ R ^ 2 / ε := by
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (sq_nonneg R) hε.le)).mpr
  intro i
  change |a i ^ 2 * w i| ≤ R ^ 2 / ε
  apply diagonal_weight_square_bound (a i) (w i) ε R hε hR (hw i)
  exact (norm_le_pi_norm (fun i => a i * w i) i).trans hbound

end

/-! Coordinate gaps control the square of a diagonal action, in any
finite-dimensional norm obtained through continuous linear coordinates. -/

theorem diagonal_action_square_bound
    {G V ι : Type*} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι] [MulAction G V] (e : V ≃L[ℝ] (ι → ℝ))
    (a : G) (χ : ι → ℝ) (ha : ∀ w : V, ∀ i, e (a • w) i = χ i * e w i)
    (w : V) (ε R : ℝ) (hε : 0 < ε) (hR : 0 ≤ R)
    (hgap : ∀ i, e w i = 0 ∨ ε ≤ |e w i|) (hbound : ‖a • w‖ ≤ R) :
    ‖(a * a) • w‖ ≤ ‖e.symm.toContinuousLinearMap‖ *
      ((‖e.toContinuousLinearMap‖ * R) ^ 2 / ε) := by
  have hfirst : ‖fun i => χ i * e w i‖ ≤ ‖e.toContinuousLinearMap‖ * R := by
    have he : (fun i => χ i * e w i) = e (a • w) := funext (fun i => (ha w i).symm)
    rw [he]
    exact (e.toContinuousLinearMap.le_opNorm (a • w)).trans
      (mul_le_mul_of_nonneg_left hbound (norm_nonneg _))
  have hsq := diagonal_weight_square_pi_bound χ (e w) ε (‖e.toContinuousLinearMap‖ * R)
    hε (mul_nonneg (norm_nonneg _) hR) hgap hfirst
  have he : e ((a * a) • w) = fun i => χ i ^ 2 * e w i := by
    ext i
    rw [mul_smul, ha, ha]
    ring
  calc
    ‖(a * a) • w‖ = ‖e.symm (e ((a * a) • w))‖ := by rw [e.symm_apply_apply]
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e ((a * a) • w)‖ := e.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * ((‖e.toContinuousLinearMap‖ * R) ^ 2 / ε) := by
      rw [he]
      exact mul_le_mul_of_nonneg_left hsq (norm_nonneg _)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalActionSquareBound.Construction
