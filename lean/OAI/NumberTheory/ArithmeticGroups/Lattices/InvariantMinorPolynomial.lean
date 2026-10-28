import OAI.NumberTheory.ArithmeticGroups.Lattices.DerivationMatrixDeterminant
import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixDifferential
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.PolynomialConstants

/-! # Invariant Minor Polynomial -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantMinorPolynomial.Construction

noncomputable section

/-! Maximal minors of an invariant frame are infinitesimally constant
when the induced matrix on the frame has trace zero. -/

open scoped Classical
open _root_.MvPolynomial

def polynomialColumnMatrix {k : Type} [Field k] {n r : ℕ}
    (U : Matrix (Fin n) (Fin r) k) : Matrix (Fin n) (Fin r) (Algebraic.CoordinatePolynomial n k) :=
  Matrix.of (fun i j => MatrixDifferential.Construction.matrixVectorPolynomial (fun a => U a j) i)

def frameMinorPolynomial {k : Type} [Field k] {n r : ℕ}
    (U : Matrix (Fin n) (Fin r) k) (rows : Fin r → Fin n) : Algebraic.CoordinatePolynomial n k :=
  ((polynomialColumnMatrix U).submatrix rows id).det

theorem derivative_polynomialColumnMatrix
    {k : Type} [Field k] {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (U : Matrix (Fin n) (Fin r) k)
    (C : Matrix (Fin r) (Fin r) k) (hU : A * U = U * C) (i : Fin n) (j : Fin r) :
    Infinitesimal.Action.Construction.rightInfinitesimal A (polynomialColumnMatrix U i j) =
      (polynomialColumnMatrix U *
        (MvPolynomial.C.mapMatrix C : Matrix (Fin r) (Fin r) (Algebraic.CoordinatePolynomial n k))) i j := by
  change Infinitesimal.Action.Construction.rightInfinitesimal A (MatrixDifferential.Construction.matrixVectorPolynomial (fun a => U a j) i) = _
  rw [MatrixDifferential.Construction.derivative_matrixVectorPolynomial]
  have hv : A.mulVec (fun a => U a j) = fun a => (U * C) a j := by
    change (fun a => (A * U) a j) = _
    rw [hU]
  rw [hv]
  simp only [MatrixDifferential.Construction.matrixVectorPolynomial, polynomialColumnMatrix, Matrix.of_apply, Matrix.mul_apply,
    RingHom.mapMatrix_apply, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem derivative_frameMinorPolynomial
    {k : Type} [Field k] {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (U : Matrix (Fin n) (Fin r) k)
    (C : Matrix (Fin r) (Fin r) k) (hU : A * U = U * C) (hC : C.trace = 0)
    (rows : Fin r → Fin n) : Infinitesimal.Action.Construction.rightInfinitesimal A (frameMinorPolynomial U rows) = 0 := by
  have hD : ∀ i j,
      Infinitesimal.Action.Construction.rightInfinitesimal A (((polynomialColumnMatrix U).submatrix rows id) i j) =
        (((polynomialColumnMatrix U).submatrix rows id) *
          (MvPolynomial.C.mapMatrix C : Matrix (Fin r) (Fin r) (Algebraic.CoordinatePolynomial n k))) i j := by
    intro i j
    exact derivative_polynomialColumnMatrix A U C hU (rows i) j
  have hc : (MvPolynomial.C.mapMatrix C : Matrix (Fin r) (Fin r) (Algebraic.CoordinatePolynomial n k)).trace = 0 := by
    change (∑ i, MvPolynomial.C (C i i)) = 0
    rw [← map_sum]
    change MvPolynomial.C C.trace = 0
    rw [hC, map_zero]
  change (Infinitesimal.Action.Construction.rightInfinitesimal A) (((polynomialColumnMatrix U).submatrix rows id).det) = 0
  rw [DerivationMatrixDeterminant.Construction.derivation_det_of_entry_eq_mul (Infinitesimal.Action.Construction.rightInfinitesimal A) _ _ hD, hc, mul_zero]

theorem group_preserves_frame_minors
    {k K : Type} [Field k] [CharZero k] [Field K] {n r : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (U : Matrix (Fin n) (Fin r) k)
    (hU : ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G,
      ∃ C : Matrix (Fin r) (Fin r) k, A * U = U * C ∧ C.trace = 0)
    (rows : Fin r → Fin n) (ι : k →+* K) (g : G.Points ι) :
    Algebraic.evaluateMatrix ι g.val (frameMinorPolynomial U rows) =
      ι (Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (frameMinorPolynomial U rows)) := by
  apply Infinitesimal.PolynomialConstants.Construction.evaluate_infinitesimal_invariant_constant G hG
  intro A hA
  obtain ⟨C, hAC, hC⟩ := hU A hA
  rw [derivative_frameMinorPolynomial A U C hAC hC rows]
  exact (VanishingIdeal.Construction.coordinateVanishingIdeal G).zero_mem

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantMinorPolynomial.Construction
