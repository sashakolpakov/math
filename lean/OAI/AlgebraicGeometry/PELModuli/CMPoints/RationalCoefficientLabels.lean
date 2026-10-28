import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodCoordinates
import Mathlib.LinearAlgebra.Countable

/-! # Rational Coefficient Labels -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.RationalCoefficientLabels

noncomputable section

/-! A rational marking and Hermitian matrix form a countable label.
A complex normalizer is chosen once for each matrix label. -/

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

def RationalCoefficientLabel (n : ℕ) :=
  {q : ((Fin n → ℚ) ≃ₗ[ℚ] (Fin 3 → E)) × Matrix (Fin 3) (Fin 3) E //
    (∀ i j, q.2 i j = NumberField.IsCMField.complexConj E (q.2 j i)) ∧
    ∃ e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec, ∀ x y,
      AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ q.2 (e x) (e y) =
        AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y}

instance rationalCoefficientLabel_countable (n : ℕ) : Countable (RationalCoefficientLabel P n) := by
  let : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable ((Fin n → ℚ) →ₗ[ℚ] (Fin 3 → E)) :=
    Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable ((Fin n → ℚ) ≃ₗ[ℚ] (Fin 3 → E)) :=
    Function.Injective.countable (f := fun e => e.toLinearMap) (fun _ _ h => LinearEquiv.toLinearMap_injective h)
  let : Countable (Matrix (Fin 3) (Fin 3) E) := inferInstanceAs (Countable (Fin 3 → Fin 3 → E))
  exact Function.Injective.countable (f := fun i : RationalCoefficientLabel P n => i.val)
    Subtype.val_injective

namespace RationalCoefficientLabel

variable {P} {n : ℕ} (i : RationalCoefficientLabel P n)

def normalizer : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec := i.property.2.choose

theorem normalizer_spec (x y : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ i.val.2 (i.normalizer x) (i.normalizer y) =
      AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y :=
  i.property.2.choose_spec x y

def coordinates (hP : P.IsAdmissible) : (Fin n → ℂ) ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) :=
  (TensorProduct.piScalarRight ℚ ℂ ℂ (Fin n)).symm.trans
    ((i.val.1.baseChange ℚ ℂ _ _).trans (PeriodCoordinates.cmPeriodCoordinates P hP))

end RationalCoefficientLabel

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.RationalCoefficientLabels
