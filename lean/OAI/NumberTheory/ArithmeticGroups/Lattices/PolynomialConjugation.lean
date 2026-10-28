import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixDifferential
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Action

/-! # Polynomial Conjugation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialConjugation.Construction

noncomputable section

/-! Conjugation of matrix coordinate polynomials and its effect on the
infinitesimal right action. -/

def polynomialConjugation {k : Type} [Field k] {n : ℕ} (g : Algebraic.SL n k) :
    Algebraic.CoordinatePolynomial n k →ₐ[k] Algebraic.CoordinatePolynomial n k :=
  (LeftTranslation.Construction.leftTranslate (g : Matrix (Fin n) (Fin n) k)).comp
    (PolynomialAction.Construction.rightTranslate ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k))

theorem rightTranslate_evaluate_rational {k : Type} [Field k] {n : ℕ}
    (g x : Algebraic.SL n k) (p : Algebraic.CoordinatePolynomial n k) :
    Algebraic.evaluateMatrix (RingHom.id k) x (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k) p) =
      Algebraic.evaluateMatrix (RingHom.id k) (x * g) p := by
  have hg : Matrix.SpecialLinearGroup.map (RingHom.id k) g = g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl
  rw [PolynomialAction.Construction.rightTranslate_evaluate, hg]

theorem evaluate_polynomialConjugation {k : Type} [Field k] {n : ℕ}
    (g x : Algebraic.SL n k) (p : Algebraic.CoordinatePolynomial n k) :
    Algebraic.evaluateMatrix (RingHom.id k) x (polynomialConjugation g p) =
      Algebraic.evaluateMatrix (RingHom.id k) (g * x * g⁻¹) p := by
  change Algebraic.evaluateMatrix (RingHom.id k) x
    (LeftTranslation.Construction.leftTranslate (g : Matrix (Fin n) (Fin n) k)
      (PolynomialAction.Construction.rightTranslate ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) p)) = _
  rw [MatrixDifferential.Construction.leftTranslate_evaluate_rational, rightTranslate_evaluate_rational]

theorem rightInfinitesimal_rightTranslate_inv {k : Type} [Field k] {n : ℕ}
    (g : Algebraic.SL n k) (A : Matrix (Fin n) (Fin n) k) (p : Algebraic.CoordinatePolynomial n k) :
    Infinitesimal.Action.Construction.rightInfinitesimal A (PolynomialAction.Construction.rightTranslate ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) p) =
      PolynomialAction.Construction.rightTranslate ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k)
        (Infinitesimal.Action.Construction.rightInfinitesimal ((g : Matrix (Fin n) (Fin n) k) * A *
          ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k)) p) := by
  let e := PolynomialAction.Construction.rightTranslateEquiv g
  have he := congrArg (fun D : Derivation k (Algebraic.CoordinatePolynomial n k) (Algebraic.CoordinatePolynomial n k) =>
    D p) (Infinitesimal.Action.Construction.rightInfinitesimal_conjugation g A)
  change Infinitesimal.Action.Construction.rightInfinitesimal ((g : Matrix (Fin n) (Fin n) k) * A *
    ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k)) p =
    e (Infinitesimal.Action.Construction.rightInfinitesimal A (e.symm p)) at he
  have hh := congrArg e.symm he
  rw [AlgEquiv.symm_apply_apply] at hh
  exact hh.symm

theorem derivative_polynomialConjugation {k : Type} [Field k] {n : ℕ}
    (g : Algebraic.SL n k) (A : Matrix (Fin n) (Fin n) k) (p : Algebraic.CoordinatePolynomial n k) :
    Infinitesimal.Action.Construction.rightInfinitesimal A (polynomialConjugation g p) =
      polynomialConjugation g
        (Infinitesimal.Action.Construction.rightInfinitesimal ((g : Matrix (Fin n) (Fin n) k) * A *
          ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k)) p) := by
  change Infinitesimal.Action.Construction.rightInfinitesimal A (LeftTranslation.Construction.leftTranslate (g : Matrix (Fin n) (Fin n) k)
    (PolynomialAction.Construction.rightTranslate ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) p)) = _
  rw [LeftTranslation.Construction.rightInfinitesimal_leftTranslate, rightInfinitesimal_rightTranslate_inv]
  rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialConjugation.Construction
