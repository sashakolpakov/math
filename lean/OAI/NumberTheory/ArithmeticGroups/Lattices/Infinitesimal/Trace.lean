import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Action
import OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateIdeal

/-! # Trace -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Trace.Construction

noncomputable section

/-! Infinitesimal matrix directions preserving the determinant-one
equation have trace zero. -/

open scoped Classical
open _root_.MvPolynomial

variable {k : Type} [Field k] {n : ℕ}

def infinitesimalCurve (A : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) (Polynomial k) :=
  1 + (Polynomial.X : Polynomial k) • Polynomial.C.mapMatrix A

def infinitesimalCurveEval (A : Matrix (Fin n) (Fin n) k) :
    Algebraic.CoordinatePolynomial n k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval (fun ij => infinitesimalCurve A ij.1 ij.2)

@[simp] theorem infinitesimalCurveEval_X (A : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    infinitesimalCurveEval A (MvPolynomial.X (i, j)) = infinitesimalCurve A i j := by
  simp [infinitesimalCurveEval]

@[simp] theorem infinitesimalCurve_entry_eval_zero (A : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    (infinitesimalCurve A i j).eval 0 = (1 : Matrix (Fin n) (Fin n) k) i j := by
  by_cases hij : i = j <;>
    simp [infinitesimalCurve, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hij]

@[simp] theorem infinitesimalCurve_entry_derivative_eval_zero
    (A : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    (infinitesimalCurve A i j).derivative.eval 0 = A i j := by
  by_cases hij : i = j <;>
    simp [infinitesimalCurve, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hij]

theorem infinitesimalCurveEval_eval_zero (A : Matrix (Fin n) (Fin n) k)
    (p : Algebraic.CoordinatePolynomial n k) :
    (infinitesimalCurveEval A p).eval 0 = Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) p := by
  have he : (Polynomial.evalRingHom 0).comp (infinitesimalCurveEval A).toRingHom =
      Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [infinitesimalCurveEval, Algebraic.evaluateMatrix]
    · rintro ⟨i, j⟩
      simp [Algebraic.evaluateMatrix]
  exact RingHom.congr_fun he p

theorem infinitesimalCurveEval_derivative_eval_zero (A : Matrix (Fin n) (Fin n) k)
    (p : Algebraic.CoordinatePolynomial n k) :
    (infinitesimalCurveEval A p).derivative.eval 0 =
      Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (Action.Construction.rightInfinitesimal A p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [infinitesimalCurveEval, Algebraic.evaluateMatrix]
  | add p q hp hq =>
      simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p ij hp =>
      rcases ij with ⟨i, j⟩
      rw [map_mul, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_mul, hp, infinitesimalCurveEval_X, infinitesimalCurve_entry_eval_zero,
        infinitesimalCurve_entry_derivative_eval_zero, infinitesimalCurveEval_eval_zero]
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
        Action.Construction.evaluate_rightInfinitesimal_X]
      have hX : Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (MvPolynomial.X (i, j)) =
          (1 : Matrix (Fin n) (Fin n) k) i j := by simp [Algebraic.evaluateMatrix]
      rw [hX]
      ring

theorem infinitesimalCurveEval_determinantEquation (A : Matrix (Fin n) (Fin n) k) :
    infinitesimalCurveEval A (CoordinateIdeal.Construction.determinantEquation k n) = (infinitesimalCurve A).det - 1 := by
  let M : Matrix (Fin n) (Fin n) (Algebraic.CoordinatePolynomial n k) := fun i j => MvPolynomial.X (i, j)
  have he := (infinitesimalCurveEval A).toRingHom.map_det M
  have hM : (infinitesimalCurveEval A).toRingHom.mapMatrix M = infinitesimalCurve A := by
    ext i j : 1
    change infinitesimalCurveEval A (MvPolynomial.X (i, j)) = infinitesimalCurve A i j
    exact infinitesimalCurveEval_X A i j
  rw [hM] at he
  change infinitesimalCurveEval A (M.det - 1) = _
  rw [map_sub, map_one]
  exact congrArg (fun p : Polynomial k => p - 1) he

theorem evaluate_rightInfinitesimal_determinantEquation (A : Matrix (Fin n) (Fin n) k) :
    Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k)
      (Action.Construction.rightInfinitesimal A (CoordinateIdeal.Construction.determinantEquation k n)) = A.trace := by
  rw [← infinitesimalCurveEval_derivative_eval_zero, infinitesimalCurveEval_determinantEquation,
    Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero]
  exact Matrix.derivative_det_one_add_X_smul A

theorem infinitesimalStabilizer_trace_zero (G : Algebraic.MatrixAlgebraicGroup k n)
    {A : Matrix (Fin n) (Fin n) k} (hA : A ∈ Action.Construction.infinitesimalStabilizer G) : A.trace = 0 := by
  have hp : CoordinateIdeal.Construction.determinantEquation k n ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G :=
    CoordinateIdeal.Construction.definingIdeal_le_vanishingIdeal G (Ideal.subset_span (Set.mem_insert _ _))
  have h := (Action.Construction.mem_infinitesimalStabilizer G A).mp hA _ hp k (RingHom.id k)
    (1 : G.Points (RingHom.id k))
  simpa only [OneMemClass.coe_one, evaluate_rightInfinitesimal_determinantEquation] using h

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Trace.Construction
