import OAI.ArithmeticGeometry.Models.CoefficientSystem
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # Coefficient Fields -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CoefficientFields

noncomputable section

/-! Finite sets of coefficients in an algebraic extension of a number
field already form a number field. The original coefficient algebra and
its inclusion into the ambient field are retained. -/

open OAI.ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [Algebra.IsIntegral K L] (s : Finset L)

theorem algebraicCoefficientRing_finite : Module.Finite K (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet
    (fun x _ => Algebra.IsIntegral.isIntegral x)

@[instance_reducible]
def algebraicCoefficientField : Field (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s) := by
  have : Algebra.IsIntegral K (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s) :=
    Algebra.IsIntegral.of_injective (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s).val Subtype.val_injective
  exact (isField_of_isIntegral_of_isField' (R := K) (S := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s)
    (Field.toIsField K)).toField

theorem algebraicCoefficientNumberField [NumberField K] :
    letI := algebraicCoefficientField K L s
    NumberField (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s) := by
  let := algebraicCoefficientField K L s
  have : CharZero (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s) :=
    CharZero.of_addMonoidHom (algebraMap K (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s)).toAddMonoidHom
      (by simp) (RingHom.injective _)
  have : Module.Finite K (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s) := algebraicCoefficientRing_finite K L s
  exact { to_finiteDimensional := Module.Finite.trans K (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing K L s) }

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CoefficientFields
