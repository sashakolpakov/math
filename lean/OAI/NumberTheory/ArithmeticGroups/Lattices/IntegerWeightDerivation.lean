import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Action

/-! # Integer Weight Derivation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.IntegerWeightDerivation.Construction

noncomputable section

/-! The Euler derivation for arbitrary integer weights agrees with
right infinitesimal translation by an integer diagonal matrix. -/

open scoped Classical
open _root_.MvPolynomial

theorem sum_polynomial_derivations_apply
    {k σ ι : Type*} [Field k] (s : Finset ι)
    (D : ι → Derivation k (MvPolynomial σ k) (MvPolynomial σ k)) (p : MvPolynomial σ k) :
    (∑ i ∈ s, D i) p = ∑ i ∈ s, D i p := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Derivation.zero_apply]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Derivation.add_apply, ih]

def integerWeightDerivation {k σ : Type*} [Field k] [Fintype σ] (w : σ → ℤ) :
    Derivation k (MvPolynomial σ k) (MvPolynomial σ k) :=
  ∑ i, (C (w i : k) * X i) • pderiv i

theorem integerWeightDerivation_apply {k σ : Type*} [Field k] [Fintype σ]
    (w : σ → ℤ) (p : MvPolynomial σ k) :
    integerWeightDerivation w p = ∑ i, (w i : k) • (X i * pderiv i p) := by
  unfold integerWeightDerivation
  rw [sum_polynomial_derivations_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Derivation.smul_apply, smul_eq_mul, MvPolynomial.smul_eq_C_mul, mul_assoc]

theorem integerWeightDerivation_X {k σ : Type*} [Field k] [Fintype σ]
    (w : σ → ℤ) (i : σ) :
    integerWeightDerivation (k := k) w (X i) = C (w i : k) * X i := by
  rw [integerWeightDerivation_apply]
  simp [MvPolynomial.pderiv_X, Pi.single_apply, MvPolynomial.smul_eq_C_mul]

theorem rightInfinitesimal_integer_diagonal
    {k : Type} [Field k] {n : ℕ} (w : Fin n → ℤ) :
    Infinitesimal.Action.Construction.rightInfinitesimal (Matrix.diagonal (fun i => (w i : k))) =
      integerWeightDerivation (fun ij : Fin n × Fin n => w ij.2) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨i, j⟩
  rw [integerWeightDerivation_X, Infinitesimal.Action.Construction.rightInfinitesimal_X]
  simp only [Matrix.diagonal_apply, apply_ite MvPolynomial.C, map_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact mul_comm _ _

theorem integerWeightDerivation_monomial
    {k σ : Type*} [Field k] [Fintype σ] (w : σ → ℤ) (m : σ →₀ ℕ) (c : k) :
    integerWeightDerivation w (monomial m c) = (Finsupp.weight w m : k) • monomial m c := by
  rw [integerWeightDerivation_apply]
  simp only [MvPolynomial.X_mul_pderiv_monomial, ← Nat.cast_smul_eq_nsmul k,
    smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Finsupp.weight_eq_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  exact mul_comm _ _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.IntegerWeightDerivation.Construction
