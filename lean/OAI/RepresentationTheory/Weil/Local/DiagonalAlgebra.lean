import OAI.RepresentationTheory.Weil.Local.DiagonalQuadratic
import OAI.RepresentationTheory.Weil.Local.SymmetricSquareLift

/-! # Diagonal Algebra -/

namespace OAI.RepresentationTheory.Weil.Local.DiagonalAlgebra.Construction

noncomputable section

/-! Nonsingular diagonal matrices, quadratic identities, and their Haar factors. -/

open _root_.Matrix

def diagonalGeneralLinear {k : Type} [Field k] {n : ℕ} (a : Fin n → kˣ) : FunctionsMetaplectic.Construction.GeneralLinear k n where
  val := diagonal (fun i => (a i).val)
  inv := diagonal (fun i => ((a i)⁻¹).val)
  val_inv := by simp [diagonal_mul_diagonal]
  inv_val := by simp [diagonal_mul_diagonal]

theorem diagonalGeneralLinear_inv {k : Type} [Field k] {n : ℕ} (a : Fin n → kˣ) :
    (diagonalGeneralLinear a)⁻¹ = diagonalGeneralLinear (fun i => (a i)⁻¹) := by
  apply Units.ext
  rfl

theorem diagonalGeneralLinear_inverse_mulVec {k : Type} [Field k] {n : ℕ}
    (a : Fin n → kˣ) (x : FunctionsMetaplectic.Construction.Position k n) :
    (diagonalGeneralLinear a)⁻¹.val *ᵥ x = fun i => x i / (a i).val := by
  ext i
  change (diagonal (fun i => ((a i)⁻¹).val) *ᵥ x) i = _
  rw [mulVec_diagonal, Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm]

theorem diagonal_quadratic_inverse_substitution {k : Type} [Field k] {n : ℕ}
    (a : Fin n → kˣ) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) (fun i => x i / (a i).val) =
      FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) x := by
  rw [RealDiagonalFresnel.Construction.quadratic_diagonal, RealDiagonalFresnel.Construction.quadratic_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

theorem diagonalGeneralLinear_determinant
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    {n : ℕ} (a : Fin n → kˣ) : FunctionsMetaplectic.Construction.determinantUnit k (diagonalGeneralLinear a) = ∏ i, a i := by
  apply Units.ext
  simp [FunctionsMetaplectic.Construction.determinantUnit, diagonalGeneralLinear, det_diagonal]

theorem localModulus_prod {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] {ι : Type} (s : Finset ι) (a : ι → kˣ) :
    FunctionsMetaplectic.Construction.localModulus k (∏ i ∈ s, a i) = ∏ i ∈ s, FunctionsMetaplectic.Construction.localModulus k (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, FunctionsMetaplectic.Construction.localModulus_one]
  | @insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, FunctionsMetaplectic.Construction.localModulus_mul, ih]

theorem diagonalGeneralLinear_modulus
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    {n : ℕ} (a : Fin n → kˣ) :
    FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k (diagonalGeneralLinear a)) = ∏ i, FunctionsMetaplectic.Construction.localModulus k (a i) := by
  rw [diagonalGeneralLinear_determinant, localModulus_prod]

theorem diagonalGaussianCoefficient_eq
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    {n : ℕ} (ψ : AddChar k ℂ) (a : Fin n → kˣ) :
    DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ a = (∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val) *
      ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k (diagonalGeneralLinear a))))⁻¹ : ℂ) := by
  rw [DiagonalQuadratic.Construction.diagonalGaussianCoefficient, Finset.prod_mul_distrib, diagonalGeneralLinear_modulus,
    Real.sqrt_prod _ (fun i _ => (FunctionsMetaplectic.Construction.localModulus_pos k (a i)).le)]
  simp only [Complex.ofReal_prod, Finset.prod_inv_distrib]

theorem diagonal_complete_square {k : Type} [Field k] [CharZero k] {n : ℕ}
    (a : Fin n → kˣ) (x y : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) (y + fun i => x i / (a i).val) -
      FunctionsMetaplectic.Construction.dot x (y + fun i => x i / (a i).val) =
        FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) y -
          FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) x := by
  simp only [RealDiagonalFresnel.Construction.quadratic_diagonal, FunctionsMetaplectic.Construction.dot, Pi.add_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  field_simp
  ring

theorem diagonal_weyl_factorization {k : Type} [Field k] {n : ℕ} (a : Fin n → kˣ) :
    Generators.Construction.quadraticSymplectic (k := k) ⟨-diagonal (fun i => ((a i)⁻¹).val), (isSymm_diagonal _).neg⟩ *
      GenerationSymplectic.Construction.upperSymplectic ⟨diagonal (fun i => (a i).val), isSymm_diagonal _⟩ *
      Generators.Construction.quadraticSymplectic ⟨-diagonal (fun i => ((a i)⁻¹).val), (isSymm_diagonal _).neg⟩ =
        Generators.Construction.leviSymplectic (diagonalGeneralLinear a) * Generators.Construction.weylSymplectic k n := by
  have hD : diagonal (fun i => (a i).val) * diagonal (fun i => ((a i)⁻¹).val) = 1 :=
    (diagonalGeneralLinear a).val_inv
  have hDi : diagonal (fun i => ((a i)⁻¹).val) * diagonal (fun i => (a i).val) = 1 :=
    (diagonalGeneralLinear a).inv_val
  apply Subtype.ext
  change fromBlocks 1 0 (-diagonal fun i => ((a i)⁻¹).val) 1 *
    fromBlocks 1 (diagonal fun i => (a i).val) 0 1 *
    fromBlocks 1 0 (-diagonal fun i => ((a i)⁻¹).val) 1 =
      (Generators.Construction.leviSymplectic (diagonalGeneralLinear a)).val * fromBlocks 0 1 (-1) 0
  rw [Generators.Construction.leviSymplectic_matrix]
  change _ = fromBlocks (diagonal fun i => (a i).val) 0 0
    (diagonal fun i => ((a i)⁻¹).val)ᵀ * fromBlocks 0 1 (-1) 0
  rw [diagonal_transpose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_multiply]
  simp only [mul_one, one_mul, zero_mul, mul_zero, zero_add, add_zero, neg_mul, mul_neg,
    hD, hDi, add_neg_cancel, neg_add_cancel, neg_zero]

end

end OAI.RepresentationTheory.Weil.Local.DiagonalAlgebra.Construction
