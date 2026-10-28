import OAI.Analysis.PDE.Elliptic.SignedFrame

open InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]

omit [FiniteDimensional ℝ E] in
theorem symmetric_quadratic_polarization (H : E →L[ℝ] E)
    (hH : H.toLinearMap.IsSymmetric) (u v : E) :
    inner ℝ (u + v) (H (u + v)) - inner ℝ (u - v) (H (u - v)) =
      4 * inner ℝ u (H v) := by
  have hs : inner ℝ v (H u) = inner ℝ u (H v) :=
    (hH v u).symm.trans (real_inner_comm _ _)
  simp only [map_add, map_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, hs]
  ring

omit [DecidableEq I] [FiniteDimensional ℝ E] in
theorem norm_le_sum_abs_matrix (b : OrthonormalBasis I ℝ E) (H : E →L[ℝ] E) :
    ‖H‖ ≤ ∑ j, ∑ i, |inner ℝ (b i) (H (b j))| := by
  calc
    ‖H‖ = ‖∑ j, ∑ i, inner ℝ (b i) (H (b j)) • rankOne ℝ (b i) (b j)‖ := by
      conv_lhs => rw [operator_rankOne_double_basis b H]
    _ ≤ ∑ j, ‖∑ i, inner ℝ (b i) (H (b j)) • rankOne ℝ (b i) (b j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ∑ i, ‖inner ℝ (b i) (H (b j)) • rankOne ℝ (b i) (b j)‖ :=
      Finset.sum_le_sum (fun _ _ ↦ norm_sum_le _ _)
    _ = _ := by simp only [norm_smul, Real.norm_eq_abs, norm_rankOne, b.norm_eq_one, mul_one]

omit [DecidableEq I] [FiniteDimensional ℝ E] in
/-- The same fixed directions used to decompose elliptic coefficients recover
the norm of every symmetric matrix. This is what upgrades directional Hölder
estimates to a full Hessian estimate. -/
theorem norm_le_signedFrame_quadratics (b : OrthonormalBasis I ℝ E)
    (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric) :
    ‖H‖ ≤ ∑ q, |inner ℝ (signedFrame b q) (H (signedFrame b q))| := by
  have hentry (i j : I) : |inner ℝ (b i) (H (b j))| ≤
      |inner ℝ (b i + b j) (H (b i + b j))| +
        |inner ℝ (b i - b j) (H (b i - b j))| := by
    have hp := symmetric_quadratic_polarization H hH (b i) (b j)
    have h₁ := neg_abs_le (inner ℝ (b i + b j) (H (b i + b j)))
    have h₂ := le_abs_self (inner ℝ (b i + b j) (H (b i + b j)))
    have h₃ := neg_abs_le (inner ℝ (b i - b j) (H (b i - b j)))
    have h₄ := le_abs_self (inner ℝ (b i - b j) (H (b i - b j)))
    rw [abs_le]
    constructor <;> linarith [abs_nonneg (inner ℝ (b i + b j) (H (b i + b j))),
      abs_nonneg (inner ℝ (b i - b j) (H (b i - b j)))]
  have hsum := (norm_le_sum_abs_matrix b H).trans
    (Finset.sum_le_sum (fun j _ ↦ Finset.sum_le_sum (fun i _ ↦ hentry i j)))
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, signedFrame]
  simp only [Finset.sum_add_distrib] at hsum
  have hbase : 0 ≤ ∑ i, |inner ℝ (b i) (H (b i))| :=
    Finset.sum_nonneg (fun i _ ↦ abs_nonneg _)
  linarith

omit [DecidableEq I] [FiniteDimensional ℝ E] in
theorem norm_le_familyFrame_quadratics
    (bs : Finset (OrthonormalBasis I ℝ E)) (hbs : bs.Nonempty)
    (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric) :
    ‖H‖ ≤ ∑ j : {b // b ∈ bs} × SignedFrameIndex I,
      |inner ℝ (signedFrame j.1.val j.2) (H (signedFrame j.1.val j.2))| := by
  classical
  obtain ⟨b, hb⟩ := hbs
  have hs := Finset.single_le_sum
    (s := (Finset.univ : Finset {b // b ∈ bs}))
    (f := fun b ↦ ∑ q, |inner ℝ (signedFrame b.val q) (H (signedFrame b.val q))|)
    (fun b _ ↦ Finset.sum_nonneg (fun q _ ↦ abs_nonneg _))
    (Finset.mem_univ (⟨b, hb⟩ : {b // b ∈ bs}))
  exact (norm_le_signedFrame_quadratics b H hH).trans (by
    simpa only [Fintype.sum_prod_type] using hs)

end OAI.Analysis.PDE.Elliptic
