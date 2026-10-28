import OAI.AlgebraicGeometry.PELModuli.CMPoints.CoordinateFibers
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralModel
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HodgePiFactorization

/-! # Factorization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The chosen coordinate CM fiber has three constructed rank-one CM
factors with full actual integral actions and algebraic splitting maps. -/

open _root_.CategoryTheory

theorem Factorization.exists_coordinate_CM_integral_factorization
    (hCMAbelianVariety : Descent.AbelianInput)
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (PeriodCoordinates.coordinateCMHodge P hP)) :
    ∃ S : ∀ i : Fin 3, IntegralModel.CMIntegralModel (PeriodCoordinates.coordinateCMType P hP i),
      (∀ i, ArithmeticGeometry.Descent.CMVariety.AbelianFiber.HasNumberFieldModel (S i).realization.abelianVariety) ∧
      Nonempty (HodgePiFactorization.ScalarFactorization R.abelianVariety
        (fun i => (S i).realization.abelianVariety)) := by
  let S (i : Fin 3) := Classical.choice (IntegralModel.exists_CM_integral_model (PeriodCoordinates.coordinateCMType P hP i))
  refine ⟨S, fun i => hCMAbelianVariety _ (S i).hasCMH1, ?_⟩
  exact HodgePiFactorization.exists_hodgePi_scalar_factorization
    (fun i => (PeriodCoordinates.coordinateCMType P hP i).hodgeStructure) R (fun i => (S i).realization)

theorem CoordinateRealization.HasCoordinateCMRealization.exists_integral_factorization
    (hCMAbelianVariety : Descent.AbelianInput)
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {hP : P.IsAdmissible} {A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (hA : CoordinateRealization.HasCoordinateCMRealization P hP A) :
    ∃ S : ∀ i : Fin 3, IntegralModel.CMIntegralModel (PeriodCoordinates.coordinateCMType P hP i),
      (∀ i, ArithmeticGeometry.Descent.CMVariety.AbelianFiber.HasNumberFieldModel (S i).realization.abelianVariety) ∧
      Nonempty (HodgePiFactorization.ScalarFactorization A (fun i => (S i).realization.abelianVariety)) := by
  obtain ⟨R, rfl⟩ := hA
  exact Factorization.exists_coordinate_CM_integral_factorization hCMAbelianVariety P hP R

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
