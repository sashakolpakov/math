import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnitriangularMatrices
import OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalChamberRatios

/-! # Upper Diagonal Conjugation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Diagonal conjugation preserves upper unitriangular matrices and
has a uniform coordinate bound when its upper-triangular ratios are bounded. -/

open _root_.Matrix
open scoped Classical

theorem UpperDiagonalConjugation.Construction.diagonal_conjugation_entry {n : ℕ} (d : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (diagonal d * M * diagonal (fun i => (d i)⁻¹)) i j = (d i / d j) * M i j := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, div_eq_mul_inv]
  ring

theorem UpperUnitriangularMatrices.Construction.IsUpperUnitriangular.diagonal_conjugation {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular M) (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) :
    UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (diagonal d * M * diagonal (fun i => (d i)⁻¹)) := by
  constructor
  · intro i j hij
    rw [UpperDiagonalConjugation.Construction.diagonal_conjugation_entry, hM.1 hij, mul_zero]
  · intro i
    rw [UpperDiagonalConjugation.Construction.diagonal_conjugation_entry, div_self (hd i), hM.2, one_mul]

theorem UpperDiagonalConjugation.Construction.diagonal_conjugation_entry_bound {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsUpperTriangular)
    (c R : ℝ) (hc : 0 ≤ c) (hR : 0 ≤ R)
    (hbound : ∀ i j, |M i j| ≤ c) (hratio : ∀ i j, i ≤ j → d i / d j ≤ R)
    (i j : Fin n) : |(diagonal d * M * diagonal (fun i => (d i)⁻¹)) i j| ≤ R * c := by
  rw [UpperDiagonalConjugation.Construction.diagonal_conjugation_entry]
  rcases le_or_gt i j with hij | hij
  · rw [abs_mul, abs_of_pos (div_pos (hd i) (hd j))]
    exact mul_le_mul (hratio i j hij) (hbound i j) (abs_nonneg _) hR
  · rw [hM hij, mul_zero, abs_zero]
    exact mul_nonneg hR hc

theorem UpperDiagonalConjugation.Construction.reduced_diagonal_conjugation_entry_bound {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (hstep : ∀ i j, i.val + 1 = j.val → d i ≤ 2 * d j)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsUpperTriangular)
    (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ i j, |M i j| ≤ c) (i j : Fin n) :
    |(diagonal d * M * diagonal (fun i => (d i)⁻¹)) i j| ≤ (2 : ℝ) ^ n * c :=
  UpperDiagonalConjugation.Construction.diagonal_conjugation_entry_bound d hd M hM c ((2 : ℝ) ^ n) hc (by positivity)
    hbound (DiagonalChamberRatios.Construction.positive_gap_chain_ratio d hd hstep) i j

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
