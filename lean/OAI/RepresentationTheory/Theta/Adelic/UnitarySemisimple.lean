import OAI.RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel
import OAI.RepresentationTheory.Theta.Adelic.SplitUnitary
import OAI.Geometry.ComplexBall.PolynomialCurves

/-! # Unitary Semisimple -/

namespace OAI.RepresentationTheory.Theta.Adelic.UnitarySemisimple

noncomputable section

/-! The arbitrary-form unitary model becomes SL(3) over an algebraic
closure, and is therefore semisimple in the actual Zariski topology. -/

open scoped Classical

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.UnitaryAlgebraicModel
open OAI.RepresentationTheory.Theta.Adelic.SplitUnitary.Special

variable {F : Type} [Field F] [CharZero F] (d : F)
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

def unitaryGeometricEquivSL (hd : d ≠ 0) (hH : H.val.conjTranspose = H.val) :
    (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val).GeometricPoints ≃*
      Matrix.SpecialLinearGroup (Fin 3) (AlgebraicClosure F) := by
  let f := algebraMap F (AlgebraicClosure F)
  let φ := Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap d f
  let H' : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (AlgebraicClosure F) (f d)))ˣ :=
    Units.map φ.mapMatrix.toMonoidHom H
  have hH' : H'.val.conjTranspose = H'.val := by
    change (H.val.map φ).conjTranspose = H.val.map φ
    rw [← Weil.AdelicSplitting.UnitaryBase.Construction.map_conjTranspose φ (Geometry.ComplexBall.ArithmeticQuotientEquationsData.quadraticMap_star d f), hH]
  let root := IsAlgClosed.exists_pow_nat_eq (f d) (show 0 < 2 by decide)
  let r := root.choose
  have hr : r ^ 2 = f d := root.choose_spec
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hr
    exact (map_ne_zero f).mpr hd hr.symm
  exact (UnitaryAlgebraicModel.regularUnitaryEquiv (f d) H'.val).symm.trans
    (SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H' hH')

theorem unitaryAlgebraicGroup_semisimple (hd : d ≠ 0) (hH : H.val.conjTranspose = H.val) :
    (UnitaryAlgebraicModel.unitaryAlgebraicGroup d H.val).IsSemisimple :=
  Geometry.ComplexBall.PolynomialCurves.ArithmeticQuotient.semisimple_of_geometric_sl3_equiv _ (unitaryGeometricEquivSL d H hd hH)

end

end OAI.RepresentationTheory.Theta.Adelic.UnitarySemisimple
