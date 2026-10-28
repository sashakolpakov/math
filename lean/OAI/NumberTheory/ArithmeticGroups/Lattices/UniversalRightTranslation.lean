import OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialFunctionalExtension
import OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialAction

/-! # Universal Right Translation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UniversalRightTranslation.Construction

noncomputable section

/-! Right translation with a universal matrix as parameter. Applying a
linear functional to the translated polynomial gives a coordinate
polynomial in the translating matrix, over the original field. -/

open scoped Classical
open _root_.MvPolynomial

def universalRightTranslation {k : Type} [Field k] (n : ℕ) :
    Algebraic.CoordinatePolynomial n k →+* MvPolynomial (Fin n × Fin n) (Algebraic.CoordinatePolynomial n k) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    (fun ij => ∑ l : Fin n, X (ij.1, l) * C (X (l, ij.2)))

theorem universalRightTranslation_specialize
    {k K : Type} [Field k] [Field K] {n : ℕ} (ι : k →+* K)
    (g : Algebraic.SL n K) (p : Algebraic.CoordinatePolynomial n k) :
    MvPolynomial.map (Algebraic.evaluateMatrix ι g) (universalRightTranslation n p) =
      PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) K) (MvPolynomial.map ι p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [universalRightTranslation, Algebraic.evaluateMatrix]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ij hp =>
      rcases ij with ⟨i, j⟩
      simp only [map_mul, hp]
      congr 1
      simp [universalRightTranslation, Algebraic.evaluateMatrix, PolynomialAction.Construction.rightTranslate_X]

def polynomialMatrixCoefficient {k : Type} [Field k] {n : ℕ}
    (φ : Algebraic.CoordinatePolynomial n k →ₗ[k] k) (p : Algebraic.CoordinatePolynomial n k) : Algebraic.CoordinatePolynomial n k :=
  PolynomialFunctionalExtension.Construction.polynomialFunctionalMap MvPolynomial.C φ (universalRightTranslation n p)

theorem evaluate_polynomialMatrixCoefficient
    {k K : Type} [Field k] [Field K] {n : ℕ} (ι : k →+* K)
    (g : Algebraic.SL n K) (φ : Algebraic.CoordinatePolynomial n k →ₗ[k] k) (p : Algebraic.CoordinatePolynomial n k) :
    Algebraic.evaluateMatrix ι g (polynomialMatrixCoefficient φ p) =
      PolynomialFunctionalExtension.Construction.polynomialFunctionalMap ι φ
        (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) K) (MvPolynomial.map ι p)) := by
  unfold polynomialMatrixCoefficient
  rw [PolynomialFunctionalExtension.Construction.polynomialFunctionalMap_specialize, universalRightTranslation_specialize]
  have he : (Algebraic.evaluateMatrix ι g).comp MvPolynomial.C = ι := by
    ext c
    simp [Algebraic.evaluateMatrix]
  rw [he]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UniversalRightTranslation.Construction
