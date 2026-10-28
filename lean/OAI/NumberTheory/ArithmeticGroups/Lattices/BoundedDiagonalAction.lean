import OAI.NumberTheory.ArithmeticGroups.Lattices.IntegerWeightDerivation
import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedNilpotentAction
import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedMonomialBasis
import OAI.NumberTheory.ArithmeticGroups.Lattices.EigenbasisSemisimple

/-! # Bounded Diagonal Action -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedDiagonalAction.Construction

noncomputable section

/-! Diagonal matrices act semisimply on bounded coordinate polynomials. -/

open scoped Classical
open _root_.MvPolynomial

def scalarWeightDerivation {k σ : Type*} [Field k] [Fintype σ] (w : σ → k) :
    Derivation k (MvPolynomial σ k) (MvPolynomial σ k) :=
  ∑ i, (C (w i) * X i) • pderiv i

theorem scalarWeightDerivation_apply {k σ : Type*} [Field k] [Fintype σ]
    (w : σ → k) (p : MvPolynomial σ k) :
    scalarWeightDerivation w p = ∑ i, w i • (X i * pderiv i p) := by
  unfold scalarWeightDerivation
  rw [IntegerWeightDerivation.Construction.sum_polynomial_derivations_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Derivation.smul_apply, smul_eq_mul, MvPolynomial.smul_eq_C_mul, mul_assoc]

theorem scalarWeightDerivation_X {k σ : Type*} [Field k] [Fintype σ]
    (w : σ → k) (i : σ) :
    scalarWeightDerivation w (X i) = C (w i) * X i := by
  rw [scalarWeightDerivation_apply]
  simp [MvPolynomial.pderiv_X, Pi.single_apply, MvPolynomial.smul_eq_C_mul]

theorem rightInfinitesimal_diagonal
    {k : Type} [Field k] {n : ℕ} (w : Fin n → k) :
    Infinitesimal.Action.Construction.rightInfinitesimal (Matrix.diagonal w) =
      scalarWeightDerivation (fun ij : Fin n × Fin n => w ij.2) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨i, j⟩
  rw [scalarWeightDerivation_X, Infinitesimal.Action.Construction.rightInfinitesimal_X]
  simp only [Matrix.diagonal_apply, apply_ite MvPolynomial.C, map_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact mul_comm _ _

theorem scalarWeightDerivation_monomial
    {k σ : Type*} [Field k] [Fintype σ] (w : σ → k) (m : σ →₀ ℕ) (c : k) :
    scalarWeightDerivation w (monomial m c) = Finsupp.weight w m • monomial m c := by
  rw [scalarWeightDerivation_apply]
  simp only [MvPolynomial.X_mul_pderiv_monomial, ← Nat.cast_smul_eq_nsmul k,
    smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Finsupp.weight_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [nsmul_eq_mul]
  exact mul_comm _ _

theorem boundedInfinitesimal_diagonal_isSemisimple
    {k : Type} [Field k] {n : ℕ} (d : ℕ) (w : Fin n → k) :
    (Infinitesimal.Degree.Construction.boundedInfinitesimal d (Matrix.diagonal w)).IsSemisimple := by
  apply EigenbasisSemisimple.Construction.isSemisimple_of_finite_eigenbasis (BoundedMonomialBasis.Construction.boundedMonomialBasisRaw k n d) _
    (fun m => Finsupp.weight (fun ij : Fin n × Fin n => w ij.2) m.val)
  intro m
  apply Subtype.ext
  change Infinitesimal.Action.Construction.rightInfinitesimal (Matrix.diagonal w) (BoundedMonomialBasis.Construction.boundedMonomialBasisRaw k n d m).val =
    Finsupp.weight (fun ij : Fin n × Fin n => w ij.2) m.val •
      (BoundedMonomialBasis.Construction.boundedMonomialBasisRaw k n d m).val
  rw [BoundedMonomialBasis.Construction.boundedMonomialBasisRaw_val, rightInfinitesimal_diagonal,
    scalarWeightDerivation_monomial]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedDiagonalAction.Construction
