import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Trace
import OAI.NumberTheory.ArithmeticGroups.Lattices.LeftTranslation

/-! # Determinant Derivative -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.DeterminantDerivative.Construction

noncomputable section

/-! The infinitesimal derivative of the determinant at an arbitrary
matrix, expressed through the trace. -/

open scoped Classical
open _root_.MvPolynomial

variable {k : Type} [Field k] {n : ℕ}

def determinantPolynomial (k : Type) [Field k] (n : ℕ) : Algebraic.CoordinatePolynomial n k :=
  Matrix.det (fun i j : Fin n => X (i, j))

theorem eval_determinantPolynomial (B : Matrix (Fin n) (Fin n) k) :
    MvPolynomial.eval (fun ij => B ij.1 ij.2) (determinantPolynomial k n) = B.det := by
  let f := MvPolynomial.eval (fun ij : Fin n × Fin n => B ij.1 ij.2)
  have h := f.map_det (fun i j : Fin n => X (i, j))
  have hM : f.mapMatrix (fun i j : Fin n => X (i, j)) = B := by
    ext i j
    change f (X (i, j)) = B i j
    simp [f]
  rw [hM] at h
  exact h

theorem eval_one_leftTranslate (B : Matrix (Fin n) (Fin n) k) (p : Algebraic.CoordinatePolynomial n k) :
    Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (LeftTranslation.Construction.leftTranslate B p) =
      MvPolynomial.eval (fun ij => B ij.1 ij.2) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [Algebraic.evaluateMatrix]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ij hp =>
    obtain ⟨i, j⟩ := ij
    rw [map_mul, map_mul, hp]
    simp [Algebraic.evaluateMatrix, Matrix.one_apply]

theorem leftTranslate_determinantPolynomial (B : Matrix (Fin n) (Fin n) k) :
    LeftTranslation.Construction.leftTranslate B (determinantPolynomial k n) = C B.det * determinantPolynomial k n := by
  let Xmat : Matrix (Fin n) (Fin n) (Algebraic.CoordinatePolynomial n k) := fun i j => X (i, j)
  have hM : (LeftTranslation.Construction.leftTranslate B).toRingHom.mapMatrix Xmat = C.mapMatrix B * Xmat := by
    ext i j : 1
    change LeftTranslation.Construction.leftTranslate B (X (i, j)) = _
    rw [LeftTranslation.Construction.leftTranslate_X]
    rfl
  change (LeftTranslation.Construction.leftTranslate B).toRingHom Xmat.det = _
  rw [(LeftTranslation.Construction.leftTranslate B).toRingHom.map_det, hM, Matrix.det_mul, ← C.map_det]
  rfl

theorem eval_one_rightInfinitesimal_determinantPolynomial (A : Matrix (Fin n) (Fin n) k) :
    Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k)
      (Infinitesimal.Action.Construction.rightInfinitesimal A (determinantPolynomial k n)) = A.trace := by
  have h := Infinitesimal.Trace.Construction.evaluate_rightInfinitesimal_determinantEquation A
  change Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k)
    (Infinitesimal.Action.Construction.rightInfinitesimal A (determinantPolynomial k n - 1)) = A.trace at h
  simpa only [map_sub, Derivation.map_one_eq_zero, sub_zero] using h

theorem eval_rightInfinitesimal_determinantPolynomial
    (A B : Matrix (Fin n) (Fin n) k) :
    MvPolynomial.eval (fun ij => B ij.1 ij.2)
      (Infinitesimal.Action.Construction.rightInfinitesimal A (determinantPolynomial k n)) = B.det * A.trace := by
  rw [← eval_one_leftTranslate, ← LeftTranslation.Construction.rightInfinitesimal_leftTranslate,
    leftTranslate_determinantPolynomial, LeftTranslation.Construction.rightInfinitesimal_C_mul, map_mul,
    eval_one_rightInfinitesimal_determinantPolynomial]
  simp [Algebraic.evaluateMatrix]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.DeterminantDerivative.Construction
