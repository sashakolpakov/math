import OAI.RepresentationTheory.Theta.Adelic.UnitarySemisimple
import OAI.RepresentationTheory.Theta.Adelic.UnitarySplitPolynomials
import OAI.Geometry.ComplexBall.PolynomialCurves
import OAI.Geometry.ComplexBall.Curves

/-! # Unitary Connected -/

namespace OAI.RepresentationTheory.Theta.Adelic.UnitaryConnected

noncomputable section

/-! Polynomial paths from one to every geometric point prove connectedness
of the actual arbitrary-form special-unitary algebraic group. -/

open scoped Classical _root_.Polynomial

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel OAI.RepresentationTheory.Theta.Adelic.UnitarySemisimple
open OAI.RepresentationTheory.Theta.Adelic.SplitUnitary OAI.RepresentationTheory.Theta.Adelic.SplitUnitary.Special OAI.RepresentationTheory.Theta.Adelic.UnitarySplitPolynomials

variable {F : Type} [Field F] [CharZero F] (d : F)
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

theorem unitaryAlgebraicGroup_connected (hd : d ≠ 0) (hH : H.val.conjTranspose = H.val) :
    (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val).IsGeometricallyConnected := by
  let f := algebraMap F (AlgebraicClosure F)
  let φ := Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f
  let H' : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (AlgebraicClosure F) (f d)))ˣ :=
    Units.map φ.mapMatrix.toMonoidHom H
  have hH' : H'.val.conjTranspose = H'.val := by
    change (H.val.map φ).conjTranspose = H.val.map φ
    rw [← Weil.AdelicSplitting.UnitaryBase.Construction.map_conjTranspose φ (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap_star d f), hH]
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (f d) (show 0 < 2 by decide)
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hr
    exact (map_ne_zero f).mpr hd hr.symm
  let e₀ := SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H' hH'
  let e := e₀.symm.trans (UnitaryAlgebraicModel.regularUnitaryEquiv (f d) H'.val)
  let U := (SplitUnitary.plusUnits r hr hr0 H').val
  let V := (SplitUnitary.plusUnits r hr hr0 H').inv
  apply Geometry.ComplexBall.PolynomialCurves.ArithmeticQuotient.geometricallyConnected_of_polynomial_curves
  intro g
  obtain ⟨M, hM0, hM1⟩ := Geometry.ComplexBall.Curves.ArithmeticQuotient.sl3_exists_polynomial_curve (e.symm g)
  let γ : AlgebraicClosure F → (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val).GeometricPoints :=
    fun t => e (Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom t) M)
  let P := UnitarySplitPolynomials.regularPolynomialMatrix (Polynomial.C (f d)) (Polynomial.C (2⁻¹))
    (Polynomial.C ((2 * r)⁻¹)) (U.map Polynomial.C) (V.map Polynomial.C) M.val
  refine ⟨γ, P, ?_, ?_, ?_⟩
  · intro t i j
    have hγ : (γ t).val.val = UnitarySplitPolynomials.regularPolynomialMatrix (f d) (2⁻¹) ((2 * r)⁻¹) U V
        (Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom t) M).val := by
      change Geometry.ComplexBall.ArithmeticQuotientEquationsData.regularMatrix (f d)
        ((e₀.symm (Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom t) M)).val.val) = _
      rw [UnitarySplitPolynomials.specialUnitaryEquivSL_inverse_matrix]
      rfl
    have he := UnitarySplitPolynomials.regularPolynomialMatrix_map (Polynomial.C (f d)) (Polynomial.C (2⁻¹))
      (Polynomial.C ((2 * r)⁻¹)) (U.map Polynomial.C) (V.map Polynomial.C) M.val (Polynomial.evalRingHom t)
    have hc (A : Matrix (Fin 3) (Fin 3) (AlgebraicClosure F)) :
        (A.map Polynomial.C).map (Polynomial.evalRingHom t) = A := by
      ext a b
      simp
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C] at he
    have he' : P.map (Polynomial.eval t) =
        UnitarySplitPolynomials.regularPolynomialMatrix (f d) (2⁻¹) ((2 * r)⁻¹) U V (M.val.map (Polynomial.eval t)) :=
      he.trans (congrArg₂ (fun X Y : Matrix (Fin 3) (Fin 3) (AlgebraicClosure F) =>
        UnitarySplitPolynomials.regularPolynomialMatrix (f d) (2⁻¹) ((2 * r)⁻¹) X Y (M.val.map (Polynomial.eval t))) (hc U) (hc V))
    exact (congrArg (fun A : Matrix (Fin 6) (Fin 6) (AlgebraicClosure F) => A i j) hγ).trans
      (congrArg (fun A : Matrix (Fin 6) (Fin 6) (AlgebraicClosure F) => A i j) he'.symm)
  · change e (Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom 0) M) = 1
    rw [hM0, map_one]
  · change e (Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom 1) M) = g
    rw [hM1]
    exact e.apply_symm_apply g

def connectedSemisimpleUnitaryGroup (hd : d ≠ 0) (hH : H.val.conjTranspose = H.val) :
    NumberTheory.ArithmeticGroups.Lattices.Algebraic.ConnectedSemisimpleKGroup F where
  dimension := 6
  matrixGroup := UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val
  connected := unitaryAlgebraicGroup_connected d H hd hH
  semisimple := UnitarySemisimple.unitaryAlgebraicGroup_semisimple d H hd hH

end

end OAI.RepresentationTheory.Theta.Adelic.UnitaryConnected
