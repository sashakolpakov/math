import OAI.Geometry.ComplexBall.Semisimple
import OAI.Geometry.ComplexBall.PolynomialCurves
import OAI.Geometry.ComplexBall.Curves
import OAI.Geometry.ComplexBall.ArithmeticQuotientSplitUnitary

/-! # Connected -/

namespace OAI.Geometry.ComplexBall.Connected.ArithmeticQuotient

noncomputable section

/-! Geometric connectedness and the connected semisimple group required by
Lattices, for the explicit six-dimensional polynomial unitary model. -/

open scoped Classical _root_.Polynomial

variable {k : Type} [Field k] [CharZero k]

theorem unitaryAlgebraicGroup_connected (d b : k) (hd : d ≠ 0) (hb : b ≠ 0) :
    (ArithmeticQuotientSplitUnitary.unitaryAlgebraicGroup d b).IsGeometricallyConnected := by
  let f := algebraMap k (AlgebraicClosure k)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (f d) (show 0 < 2 by decide)
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hr
    exact hd (f.injective (by simpa only [map_zero] using hr.symm))
  have hb0 : f b ≠ 0 := (map_ne_zero f).mpr hb
  let e := ArithmeticQuotientSplitUnitary.splitSLToPoints (f d) r (f b) hr hr0 hb0
  apply PolynomialCurves.ArithmeticQuotient.geometricallyConnected_of_polynomial_curves
  intro g
  obtain ⟨A, hA0, hA1⟩ := Curves.ArithmeticQuotient.sl3_exists_polynomial_curve (e.symm g)
  let γ : AlgebraicClosure k → (ArithmeticQuotientSplitUnitary.unitaryAlgebraicGroup d b).GeometricPoints :=
    fun t => e (Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom t) A)
  let P := ArithmeticQuotientSplitUnitary.splitLiftMatrix (Polynomial.C (f d)) (Polynomial.C (f b))
    (Polynomial.C ((f b)⁻¹)) (Polynomial.C (2⁻¹)) (Polynomial.C ((2 * r)⁻¹)) A.val
  refine ⟨γ, P, ?_, ?_, ?_⟩
  · intro t i j
    have he := ArithmeticQuotientSplitUnitary.splitLiftMatrix_map (Polynomial.C (f d)) (Polynomial.C (f b))
      (Polynomial.C ((f b)⁻¹)) (Polynomial.C (2⁻¹)) (Polynomial.C ((2 * r)⁻¹))
      A.val (Polynomial.evalRingHom t)
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C] at he
    change (ArithmeticQuotientSplitUnitary.splitSLToPoints (f d) r (f b) hr hr0 hb0
      (Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom t) A)).val.val i j = _
    rw [ArithmeticQuotientSplitUnitary.splitSLToPoints_matrix]
    exact congrArg (fun M : Matrix (Fin 6) (Fin 6) (AlgebraicClosure k) => M i j) he.symm
  · change e (Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom 0) A) = 1
    rw [hA0, map_one]
  · change e (Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom 1) A) = g
    rw [hA1]
    exact e.apply_symm_apply g

def connectedSemisimpleUnitaryGroup (d b : k) (hd : d ≠ 0) (hb : b ≠ 0) :
    NumberTheory.ArithmeticGroups.Lattices.Algebraic.ConnectedSemisimpleKGroup k where
  dimension := 6
  matrixGroup := ArithmeticQuotientSplitUnitary.unitaryAlgebraicGroup d b
  connected := unitaryAlgebraicGroup_connected d b hd hb
  semisimple := Semisimple.ArithmeticQuotient.unitaryAlgebraicGroup_semisimple d b hd hb

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

def originalConnectedSemisimpleUnitaryGroup (b : E)
    (hb : NumberField.IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
    (δ : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) :
    NumberTheory.ArithmeticGroups.Lattices.Algebraic.ConnectedSemisimpleKGroup (ArithmeticQuotientEquationsData.RealField E) :=
  connectedSemisimpleUnitaryGroup (ArithmeticQuotientEquationsData.imaginarySquare δ hδ) (ArithmeticQuotientSplitUnitary.realCoefficient b hb)
    (fun h => (pow_ne_zero 2 hδ0) (congrArg (fun x : ArithmeticQuotientEquationsData.RealField E => (x : E)) h))
    (fun h => hb0 (congrArg (fun x : ArithmeticQuotientEquationsData.RealField E => (x : E)) h))

end

end OAI.Geometry.ComplexBall.Connected.ArithmeticQuotient
