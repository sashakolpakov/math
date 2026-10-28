import OAI.Analysis.PDE.Elliptic.FrameDecomposition

open InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]

abbrev SignedFrameIndex (I : Type*) := I ⊕ ((I × I) ⊕ (I × I))

def signedFrame (b : OrthonormalBasis I ℝ E) : SignedFrameIndex I → E
  | .inl i => b i
  | .inr (.inl p) => b p.2 + b p.1
  | .inr (.inr p) => b p.2 - b p.1

def signedCoefficient (a : I → I → ℝ) (eps : ℝ) : SignedFrameIndex I → ℝ
  | .inl i => a i i - eps * Fintype.card I
  | .inr (.inl p) => (eps + offDiagonal a p.2 p.1) / 4
  | .inr (.inr p) => (eps - offDiagonal a p.2 p.1) / 4

omit [DecidableEq I] [FiniteDimensional ℝ E] in
theorem signedFrame_sum (b : OrthonormalBasis I ℝ E) :
    (∑ q, rankOne ℝ (signedFrame b q) (signedFrame b q)) =
      (1 + 4 * (Fintype.card I : ℝ)) • ContinuousLinearMap.id ℝ E := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, signedFrame]
  rw [← signed_basis_frame_sum b]
  simp only [Finset.sum_add_distrib]
  congr 1
  congr 1 <;> exact Finset.sum_comm

omit [FiniteDimensional ℝ E] in
theorem signedFrame_representation (b : OrthonormalBasis I ℝ E)
    (a : I → I → ℝ) (ha : ∀ i j, a i j = a j i) (eps : ℝ) :
    (∑ q, signedCoefficient a eps q • rankOne ℝ (signedFrame b q) (signedFrame b q)) =
      ∑ j, ∑ i, a i j • rankOne ℝ (b i) (b j) := by
  simpa only [Fintype.sum_sum_type, Fintype.sum_prod_type, signedFrame,
    signedCoefficient, Finset.sum_add_distrib] using signed_frame_decomposition b a ha eps

theorem signedCoefficient_bounds {a : I → I → ℝ} {lam L eps : ℝ}
    (hL : 0 ≤ L) (heps : 0 ≤ eps)
    (hdiag : ∀ i, lam ≤ a i i ∧ a i i ≤ L)
    (hsmall : ∀ i j, |offDiagonal a i j| ≤ eps / 2)
    (hsize : eps * Fintype.card I ≤ lam / 2) :
    ∀ q, min (lam / 2) (eps / 8) ≤ signedCoefficient a eps q ∧
      signedCoefficient a eps q ≤ L + eps := by
  obtain ⟨hbase, hpair⟩ := frame_coefficients_lower (fun i ↦ (hdiag i).1) hsmall hsize
  rintro (i | (⟨j, i⟩ | ⟨j, i⟩))
  · change min (lam / 2) (eps / 8) ≤ a i i - eps * Fintype.card I ∧ _
    exact ⟨(min_le_left _ _).trans (hbase i), by
      dsimp only [signedCoefficient]
      have hcard : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
      nlinarith [(hdiag i).2]⟩
  · change min (lam / 2) (eps / 8) ≤ (eps + offDiagonal a i j) / 4 ∧ _
    exact ⟨(min_le_right _ _).trans (hpair i j).1, by
      dsimp only [signedCoefficient]
      have hab := abs_le.mp (hsmall i j)
      linarith [hab.2]⟩
  · change min (lam / 2) (eps / 8) ≤ (eps - offDiagonal a i j) / 4 ∧ _
    exact ⟨(min_le_right _ _).trans (hpair i j).2, by
      dsimp only [signedCoefficient]
      have hab := abs_le.mp (hsmall i j)
      linarith [hab.1]⟩

end OAI.Analysis.PDE.Elliptic
