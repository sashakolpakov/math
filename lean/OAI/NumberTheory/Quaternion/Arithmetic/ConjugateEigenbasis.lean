import OAI.NumberTheory.Quaternion.Arithmetic.IntegralSemisimpleDirections

/-! # Conjugate Eigenbasis -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ConjugateEigenbasis

noncomputable section

/-! A concrete conjugate-diagonal identity supplies the eigenbasis
needed by the integral spectral spanning theorem. -/

open scoped Classical
open _root_.Matrix

theorem conjugate_diagonal_has_eigenbasis {K : Type} [Field K] {n : ℕ}
    (S : Matrix (Fin n) (Fin n) K) (B : ArithmeticGroups.Lattices.Algebraic.SL n K) (w : Fin n → K)
    (hS : S = (B : Matrix (Fin n) (Fin n) K) * Matrix.diagonal w *
      ((B⁻¹ : ArithmeticGroups.Lattices.Algebraic.SL n K) : Matrix (Fin n) (Fin n) K)) :
    ∃ b : Module.Basis (Fin n) K (Fin n → K),
      ∀ i, Matrix.toLin' S (b i) = w i • b i := by
  let g : Matrix.GeneralLinearGroup (Fin n) K := B.toGL
  let e : (Fin n → K) ≃ₗ[K] (Fin n → K) := (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv
  let b := (Pi.basisFun K (Fin n)).map e
  refine ⟨b, fun i => ?_⟩
  change S *ᵥ ((B : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.basisFun K (Fin n) i)) =
    w i • ((B : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.basisFun K (Fin n) i))
  rw [hS, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.mul_one, ← Matrix.mulVec_mulVec]
  have hw : Matrix.diagonal w *ᵥ (Pi.basisFun K (Fin n) i) =
      w i • Pi.basisFun K (Fin n) i := by
    simp only [Pi.basisFun_apply, Matrix.diagonal_mulVec_single, mul_one]
    ext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  rw [hw, Matrix.mulVec_smul]

theorem conjugate_diagonal_mem_span_integral_polynomial_directions
    {K : Type} [Field K] [CharZero K] {n : ℕ} [Nonempty (Fin n)]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup K n) (S : Matrix (Fin n) (Fin n) K)
    (B : ArithmeticGroups.Lattices.Algebraic.SL n K) (w : Fin n → K)
    (hS : S = (B : Matrix (Fin n) (Fin n) K) * Matrix.diagonal w *
      ((B⁻¹ : ArithmeticGroups.Lattices.Algebraic.SL n K) : Matrix (Fin n) (Fin n) K))
    (hmem : S ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    S ∈ Submodule.span K (IntegralSemisimpleDirections.integralPolynomialDirections G S) := by
  obtain ⟨b, hb⟩ := conjugate_diagonal_has_eigenbasis S B w hS
  exact IntegralSemisimpleDirections.diagonalizable_mem_span_integral_polynomial_directions G S b w hb hmem

end

end OAI.NumberTheory.Quaternion.Arithmetic.ConjugateEigenbasis
