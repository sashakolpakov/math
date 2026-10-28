import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.PolynomialConstants

/-! # Conjugation Coordinate Polynomial -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ConjugationCoordinatePolynomial.Construction

noncomputable section

/-! Polynomial coordinates of conjugation by a special-linear matrix. -/

open scoped Classical
open _root_.MvPolynomial

def conjugationUniversalMatrix (k : Type) [Field k] (n : ℕ) :
    Matrix (Fin n) (Fin n) (Algebraic.CoordinatePolynomial n k) := fun i j => X (i, j)

def matrixConjugationPolynomial
    {k : Type} [Field k] {n : ℕ} (C : Matrix (Fin n) (Fin n) k) :
    Matrix (Fin n) (Fin n) (Algebraic.CoordinatePolynomial n k) :=
  conjugationUniversalMatrix k n * C.map MvPolynomial.C *
    (conjugationUniversalMatrix k n).adjugate

theorem evaluate_matrixConjugationPolynomial
    {k K : Type} [Field k] [Field K] {n : ℕ}
    (ι : k →+* K) (g : Algebraic.SL n K) (C : Matrix (Fin n) (Fin n) k) :
    (Algebraic.evaluateMatrix ι g).mapMatrix (matrixConjugationPolynomial C) =
      (g : Matrix (Fin n) (Fin n) K) * C.map ι *
        ((g⁻¹ : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K) := by
  have hX : (Algebraic.evaluateMatrix ι g).mapMatrix
      (conjugationUniversalMatrix k n) =
      (g : Matrix (Fin n) (Fin n) K) := by
    ext i j
    change Algebraic.evaluateMatrix ι g (X (i, j)) = _
    simp [Algebraic.evaluateMatrix]
  have hC : (Algebraic.evaluateMatrix ι g).mapMatrix (C.map MvPolynomial.C) = C.map ι := by
    ext i j
    simp [Algebraic.evaluateMatrix]
  rw [matrixConjugationPolynomial, map_mul, map_mul, RingHom.map_adjugate, hX, hC,
    Matrix.SpecialLinearGroup.coe_inv]

theorem evaluate_matrixConjugationPolynomial_entry
    {k K : Type} [Field k] [Field K] {n : ℕ}
    (ι : k →+* K) (g : Algebraic.SL n K) (C : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    Algebraic.evaluateMatrix ι g (matrixConjugationPolynomial C i j) =
      ((g : Matrix (Fin n) (Fin n) K) * C.map ι *
        ((g⁻¹ : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K)) i j :=
  congrArg (fun M => M i j) (evaluate_matrixConjugationPolynomial ι g C)

theorem matrixConjugationPolynomial_coefficient_map
    {k K : Type} [Field k] [Field K] {n : ℕ}
    (ι : k →+* K) (C : Matrix (Fin n) (Fin n) k) :
    (MvPolynomial.map ι).mapMatrix (matrixConjugationPolynomial C) =
      matrixConjugationPolynomial (C.map ι) := by
  have hX : (MvPolynomial.map ι).mapMatrix (conjugationUniversalMatrix k n) =
      conjugationUniversalMatrix K n := by
    ext i j : 1
    exact MvPolynomial.map_X ι (i, j)
  have hC : (MvPolynomial.map (σ := Fin n × Fin n) ι).mapMatrix (C.map MvPolynomial.C) =
      (C.map ι).map MvPolynomial.C := by
    ext i j : 1
    exact MvPolynomial.map_C ι (C i j)
  rw [matrixConjugationPolynomial, map_mul, map_mul, RingHom.map_adjugate, hX, hC]
  rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ConjugationCoordinatePolynomial.Construction
