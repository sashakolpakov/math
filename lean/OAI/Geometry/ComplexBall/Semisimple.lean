import OAI.Geometry.ComplexBall.ArithmeticQuotientSplitUnitary
import OAI.Geometry.ComplexBall.PolynomialCurves

/-! # Semisimple -/

namespace OAI.Geometry.ComplexBall.Semisimple.ArithmeticQuotient

noncomputable section

/-! Semisimplicity of the concrete unitary algebraic group, proved after
scalar extension to an algebraic closure and explicit splitting. -/

open scoped Classical

variable {k : Type} [Field k] [CharZero k]

def unitaryGeometricEquivSL (d b : k) (hd : d ≠ 0) (hb : b ≠ 0) :
    (ArithmeticQuotientSplitUnitary.unitaryAlgebraicGroup d b).GeometricPoints ≃* ArithmeticQuotientEquationsData.SL (AlgebraicClosure k) := by
  let f := algebraMap k (AlgebraicClosure k)
  let hroot := IsAlgClosed.exists_pow_nat_eq (f d) (show 0 < 2 by decide)
  let r := Classical.choose hroot
  have hr : r ^ 2 = f d := Classical.choose_spec hroot
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hr
    exact hd (f.injective (by simpa only [map_zero] using hr.symm))
  have hb0 : f b ≠ 0 := (map_ne_zero f).mpr hb
  exact (ArithmeticQuotientSplitUnitary.regularUnitaryEquiv (f d) (f b)).symm.trans
    (ArithmeticQuotientSplitUnitary.quadraticUnitaryEquivSL (f d) r (f b) hr hr0 hb0)

theorem unitaryAlgebraicGroup_semisimple (d b : k) (hd : d ≠ 0) (hb : b ≠ 0) :
    (ArithmeticQuotientSplitUnitary.unitaryAlgebraicGroup d b).IsSemisimple :=
  PolynomialCurves.ArithmeticQuotient.semisimple_of_geometric_sl3_equiv _ (unitaryGeometricEquivSL d b hd hb)

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem originalUnitaryAlgebraicGroup_semisimple (b : E)
    (hb : NumberField.IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
    (δ : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) :
    (ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup b hb δ hδ).IsSemisimple := by
  apply unitaryAlgebraicGroup_semisimple
  · intro h
    have he := congrArg (fun x : ArithmeticQuotientEquationsData.RealField E => (x : E)) h
    exact (pow_ne_zero 2 hδ0) he
  · intro h
    exact hb0 (congrArg (fun x : ArithmeticQuotientEquationsData.RealField E => (x : E)) h)

end

end OAI.Geometry.ComplexBall.Semisimple.ArithmeticQuotient
