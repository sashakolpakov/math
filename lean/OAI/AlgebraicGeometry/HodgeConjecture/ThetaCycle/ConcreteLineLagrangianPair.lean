import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationIntrinsicArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientSourceFrame

/-! # Concrete Line Lagrangian Pair -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteLineLagrangianPair.CM

noncomputable section

/-! Each actual rational approximation gives a Lagrangian pair with
its original trace scalar and its actual two multiplicity norms. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)

include hid

theorem exists_actual_approximation_lagrangian_pair :
    ∃ Q : Lagrangians.CM.LagrangianPair K D.ball D.places
      (fun j τ => FourSplittings.CM.newThetaSigns K v j (D.places.representative τ)),
      Q.delta = D.pair.delta ∧ Q.a = ConcreteApproximationIntrinsicArithmetic.CM.approximationNativeCoefficients K D A ∧
        ∀ j, (A.periods j).coordinates.a = Q.a j ∧ (A.periods j).coordinates.delta = Q.delta := by
  have hμ := ConcreteApproximationIntrinsicArithmetic.CM.approximation_native_active_signs K D hid
  have hs : ∀ j τ, if τ = D.places.distinguished ∨ FourSplittings.CM.newThetaSigns K v j (D.places.representative τ) = true
      then (HeckeCycles.ReferenceDatum.CM.embeddings K D.places τ (D.pair.delta * ConcreteApproximationIntrinsicArithmetic.CM.approximationNativeCoefficients K D A j)).im < 0
      else 0 < (HeckeCycles.ReferenceDatum.CM.embeddings K D.places τ (D.pair.delta * ConcreteApproximationIntrinsicArithmetic.CM.approximationNativeCoefficients K D A j)).im := by
    intro j τ
    by_cases he : τ = D.places.distinguished
    · subst τ
      simpa only [hμ, or_true, ite_true] using ConcreteApproximationIntrinsicArithmetic.CM.approximation_native_coefficient_signs K D A j D.places.distinguished
    · simpa only [he, false_or] using ConcreteApproximationIntrinsicArithmetic.CM.approximation_native_coefficient_signs K D A j τ
  have h := CoefficientPeriods.CM.exists_lagrangian_pair_with_coefficients K D.ball D.places
    (fun j τ => FourSplittings.CM.newThetaSigns K v j (D.places.representative τ)) D.pair.delta
    (ConcreteApproximationIntrinsicArithmetic.CM.approximationNativeCoefficients K D A) D.pair.delta_ne_zero D.pair.delta_imaginary
    (ConcreteApproximationIntrinsicArithmetic.CM.approximation_native_coefficients_nonzero K D A) (ConcreteApproximationIntrinsicArithmetic.CM.approximation_native_coefficients_fixed K D A) hs
  refine ⟨h.choose, h.choose_spec.1, h.choose_spec.2, ?_⟩
  intro j
  exact ⟨(A.coefficients j).1.trans (congrFun h.choose_spec.2 j).symm,
    (A.coefficients j).2.trans h.choose_spec.1.symm⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteLineLagrangianPair.CM
