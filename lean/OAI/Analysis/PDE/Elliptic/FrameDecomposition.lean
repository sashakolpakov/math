import OAI.Analysis.PDE.Elliptic.FrameSums

open InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {I : Type*} [Fintype I] [DecidableEq I]

def offDiagonal (a : I → I → ℝ) (i j : I) : ℝ := if i = j then 0 else a i j

omit [Fintype I] in
theorem offDiagonal_symmetric {a : I → I → ℝ} (ha : ∀ i j, a i j = a j i) :
    ∀ i j, offDiagonal a i j = offDiagonal a j i := by
  intro i j
  by_cases h : i = j
  · subst j; rfl
  · simp only [offDiagonal, h, Ne.symm h, ite_false, ha i j]

omit [FiniteDimensional ℝ E] in
theorem diagonal_offDiagonal_sum (b : I → E) (a : I → I → ℝ) :
    (∑ j, a j j • rankOne ℝ (b j) (b j)) +
      ∑ j, ∑ i, offDiagonal a i j • rankOne ℝ (b i) (b j) =
      ∑ j, ∑ i, a i j • rankOne ℝ (b i) (b j) := by
  have hsplit (i j : I) : a i j • rankOne ℝ (b i) (b j) =
      (if i = j then a j j • rankOne ℝ (b j) (b j) else 0) +
        offDiagonal a i j • rankOne ℝ (b i) (b j) := by
    by_cases h : i = j
    · subst j; simp [offDiagonal]
    · simp [offDiagonal, h]
  symm
  calc
    (∑ j, ∑ i, a i j • rankOne ℝ (b i) (b j)) =
        ∑ j, ∑ i, ((if i = j then a j j • rankOne ℝ (b j) (b j) else 0) +
          offDiagonal a i j • rankOne ℝ (b i) (b j)) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      exact hsplit i j
    _ = _ := by simp [Finset.sum_add_distrib]

omit [FiniteDimensional ℝ E] in
/-- Exact decomposition into basis directions and signed basis pairs.
The coefficients are positive whenever the diagonal is bounded below
and the off-diagonal entries are small enough. -/
theorem signed_frame_decomposition (b : OrthonormalBasis I ℝ E)
    (a : I → I → ℝ) (ha : ∀ i j, a i j = a j i) (eps : ℝ) :
    (∑ j, (a j j - eps * Fintype.card I) • rankOne ℝ (b j) (b j)) +
      (∑ j, ∑ i,
        (((eps + offDiagonal a i j) / 4) • rankOne ℝ (b i + b j) (b i + b j) +
        ((eps - offDiagonal a i j) / 4) • rankOne ℝ (b i - b j) (b i - b j))) =
      ∑ j, ∑ i, a i j • rankOne ℝ (b i) (b j) := by
  rw [signed_pair_sum_eq b (offDiagonal a) (offDiagonal_symmetric ha) eps]
  simp_rw [sub_smul]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, b.sum_rankOne_eq_id,
    ← diagonal_offDiagonal_sum b a]
  module

theorem frame_coefficients_lower {a : I → I → ℝ} {lam eps : ℝ}
    (hdiag : ∀ i, lam ≤ a i i) (hsmall : ∀ i j, |offDiagonal a i j| ≤ eps / 2)
    (hsize : eps * Fintype.card I ≤ lam / 2) :
    (∀ i, lam / 2 ≤ a i i - eps * Fintype.card I) ∧
      (∀ i j, eps / 8 ≤ (eps + offDiagonal a i j) / 4 ∧
        eps / 8 ≤ (eps - offDiagonal a i j) / 4) := by
  constructor
  · intro i; linarith [hdiag i]
  · intro i j
    have h := abs_le.mp (hsmall i j)
    constructor <;> linarith [h.1, h.2]

end OAI.Analysis.PDE.Elliptic
