import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.AutomorphismTransversal

/-! # Polyhedral Decay Bound -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PolyhedralDecayBound.Construction

noncomputable section

/-! A finite separating family of linear forms gives exponential decay
on any region where all forms are bounded below. -/

open scoped Classical

theorem norm_le_sum_abs_separating_forms
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
    (f : ι → Module.Dual ℝ E) (hf : ∀ x, (∀ i, f i x = 0) → x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ≤ C * ∑ i, |f i x| := by
  let T : E →ₗ[ℝ] (ι → ℝ) := LinearMap.pi f
  have hT : T.ker = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    apply (injective_iff_map_eq_zero T).mpr
    intro x hx
    exact hf x (fun i => congrFun hx i)
  obtain ⟨C, hC, hbound⟩ := T.exists_antilipschitzWith hT
  refine ⟨C, hC, fun x => ?_⟩
  have hnorm : ‖T x‖ ≤ ∑ i, |f i x| := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg (f i x)))).mpr
    intro i
    change ‖f i x‖ ≤ ∑ j, |f j x|
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun j _ => abs_nonneg (f j x)) (Finset.mem_univ i)
  exact (ZeroHomClass.bound_of_antilipschitz T hbound x).trans (mul_le_mul_of_nonneg_left hnorm hC.le)

theorem separating_forms_lower_bound
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
    (f : ι → Module.Dual ℝ E) (hf : ∀ x, (∀ i, f i x = 0) → x = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t → ∀ x, (∀ i, -t ≤ f i x) →
      c * ‖x‖ - 2 * Fintype.card ι * t ≤ ∑ i, f i x := by
  obtain ⟨C, hC, hbound⟩ := norm_le_sum_abs_separating_forms f hf
  refine ⟨C⁻¹, inv_pos.mpr hC, fun t ht x hx => ?_⟩
  have habs (i : ι) : |f i x| ≤ f i x + 2 * t := by
    apply abs_le.mpr
    constructor <;> linarith [hx i]
  have hsum : (∑ i, |f i x|) ≤ (∑ i, f i x) + 2 * Fintype.card ι * t := by
    calc
      _ ≤ ∑ i, (f i x + 2 * t) := Finset.sum_le_sum (fun i _ => habs i)
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have he := mul_le_mul_of_nonneg_left (hbound x) (inv_nonneg.mpr hC.le)
  rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] at he
  linarith

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PolyhedralDecayBound.Construction
