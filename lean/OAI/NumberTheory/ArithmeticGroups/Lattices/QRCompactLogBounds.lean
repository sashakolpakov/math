import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRVal
import OAI.NumberTheory.ArithmeticGroups.Lattices.AdjacentWeightBounds

/-! # QR Compact Log Bounds -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.QRCompactLogBounds.Construction

noncomputable section

/-! Compact QR logarithmic bounds and ratio bounds from adjacent
logarithmic chamber inequalities. -/

theorem compact_operatorQR_log_bound
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (C : Set (L →L[ℝ] L)ˣ) (hC : IsCompact C) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ g ∈ C, ∀ i, |OperatorQRVal.Construction.operatorQRLogDiagonal b g i| ≤ c := by
  obtain ⟨c, hc⟩ := hC.bddAbove_image (OperatorQRVal.Construction.operatorQRLogDiagonal_continuous b).norm.continuousOn
  refine ⟨max 0 c, le_max_left _ _, fun g hg i => ?_⟩
  exact (norm_le_pi_norm (OperatorQRVal.Construction.operatorQRLogDiagonal b g) i).trans
    ((hc ⟨g, hg, rfl⟩).trans (le_max_right _ _))

theorem positive_diagonal_ratio_of_log_gaps {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (t : ℝ) (ht : 0 ≤ t)
    (hstep : ∀ i j, i.val + 1 = j.val → Real.log (d i) - Real.log (d j) ≤ t)
    (i j : Fin n) (hij : i ≤ j) : d i / d j ≤ Real.exp ((n : ℝ) * t) := by
  have he := AdjacentWeightBounds.Construction.adjacent_difference_chain_bound (fun i => Real.log (d i)) t ht hstep i j hij
  calc
    d i / d j = Real.exp (Real.log (d i) - Real.log (d j)) := by
      rw [Real.exp_sub, Real.exp_log (hd i), Real.exp_log (hd j)]
    _ ≤ Real.exp ((n : ℝ) * t) := Real.exp_le_exp.mpr he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.QRCompactLogBounds.Construction
