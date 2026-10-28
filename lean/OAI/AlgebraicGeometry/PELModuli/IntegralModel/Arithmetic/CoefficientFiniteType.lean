import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Base
import OAI.ArithmeticGeometry.Models.CoefficientSystem
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Coefficient Finite Type -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Finite coefficient rings over the actual arithmetic base, and
their principal localizations, are finite-type algebras over the integers. -/

open OAI.ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations
variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}

theorem Base.ArithmeticBaseExtension.finiteType_int (B : Base.ArithmeticBaseExtension K κ) : Algebra.FiniteType ℤ B.R :=
  Algebra.FiniteType.trans (R := ℤ) (S := NumberField.RingOfIntegers B.extension.carrier)
    (A := B.R) inferInstance inferInstance

theorem Base.ArithmeticBaseExtension.coefficientRing_finiteType_int (B : Base.ArithmeticBaseExtension K κ)
    {F : Type} [Field F] [Algebra B.R F] (s : Finset F) :
    Algebra.FiniteType ℤ (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R F s) := by
  have hR := RingHom.finiteType_algebraMap.mpr (Base.ArithmeticBaseExtension.finiteType_int B)
  have hS := RingHom.finiteType_algebraMap.mpr (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing_finiteType B.R F s)
  have h := hS.comp hR
  have he : (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R F s)).comp (algebraMap ℤ B.R) =
      algebraMap ℤ (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R F s) := Subsingleton.elim _ _
  exact RingHom.finiteType_algebraMap.mp (he ▸ h)

theorem Base.ArithmeticBaseExtension.coefficientAway_finiteType_int (B : Base.ArithmeticBaseExtension K κ)
    {F : Type} [Field F] [Algebra B.R F] (s : Finset F) (r : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R F s) :
    Algebra.FiniteType ℤ (Localization.Away r) :=
  Algebra.FiniteType.trans (Base.ArithmeticBaseExtension.coefficientRing_finiteType_int B s)
    (inferInstanceAs (Algebra.FiniteType (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R F s) (Localization.Away r)))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
