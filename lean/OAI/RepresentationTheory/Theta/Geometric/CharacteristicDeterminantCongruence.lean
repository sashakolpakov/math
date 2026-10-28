import OAI.RepresentationTheory.Theta.Geometric.IntegralCharacteristicCoefficients
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Characteristic Determinant Congruence -/

namespace OAI.RepresentationTheory.Theta.Geometric.CharacteristicDeterminantCongruence

noncomputable section

/-! Integral characteristic coefficients suffice for determinant
congruence. No integrality of the chosen field-basis matrix entries is
required: the reversed characteristic polynomial gives the quotient. -/

open _root_.Polynomial

theorem integral_polynomial_eval {R : Type*} [CommRing R] (p : R[X])
    (hp : ∀ n, IsIntegral ℤ (p.coeff n)) (x : R) (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (p.eval x) := by
  rw [Polynomial.eval_eq_sum]
  exact IsIntegral.sum _ (fun n _ => (hp n).mul (hx.pow n))

theorem characteristic_determinant_congruence {E I : Type*} [Field E] [CharZero E]
    [Fintype I] [DecidableEq I] (M : Matrix I I E)
    (hc : ∀ n, IsIntegral ℤ (M.charpoly.coeff n)) (N : ℕ) :
    ∃ a : E, IsIntegral ℤ a ∧ (1 + (N : E) • M).det = 1 + (N : E) * a := by
  let p := M.charpolyRev
  have hp (n) : IsIntegral ℤ (p.coeff n) := by
    change IsIntegral ℤ (M.charpolyRev.coeff n)
    rw [← M.reverse_charpoly, Polynomial.coeff_reverse]
    exact hc _
  have hd (n) : IsIntegral ℤ (p.divX.coeff n) := by
    rw [coeff_divX]
    exact hp _
  have hp0 : p.coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero]
    exact Matrix.eval_charpolyRev
  have hpoly := congrArg (Polynomial.eval (-(N : E))) p.divX_mul_X_add
  simp only [eval_add, eval_mul, eval_X, eval_C, hp0] at hpoly
  have hm : p.eval (-(N : E)) = (1 + (N : E) • M).det := by
    change (Polynomial.eval (-(N : E))) (1 - (X : E[X]) • M.map C).det = _
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    apply congrArg Matrix.det
    ext i j
    simp [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
    by_cases hij : i = j <;> simp [hij, mul_comm]
  refine ⟨-p.divX.eval (-(N : E)), (integral_polynomial_eval p.divX hd _ (isIntegral_natCast N).neg).neg, ?_⟩
  rw [← hm, ← hpoly]
  ring

end

end OAI.RepresentationTheory.Theta.Geometric.CharacteristicDeterminantCongruence
