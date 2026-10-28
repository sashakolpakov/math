import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationComplexComponents
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientSourceFrame

/-! # Concrete Approximation Geometric Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationGeometricFrame.CM

noncomputable section

/-! Each actual split source frame maps to its native frame on the
fixed original tensor space through one constant invertible coefficient
map. The rational multiplicity basis is the given approximation basis. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)

theorem exists_actual_approximation_geometric_frame :
    ∃ C : (PeriodTotal.CM.TotalPositions K D.places → ℂ) ≃ₗ[ℂ] (Fin D.places.count × (Fin 3 × Fin 2) → ℂ),
      ∀ (z : D.ball.Domain) (u : PeriodTotal.CM.TotalPositions K D.places → ℂ),
        ConcreteApproximationComplexComponents.CM.approximationComplexComponents K D A hid (ComplexTransition.CM.complexTensorBasisChange K A.basis
          (AdaptedTotal.CM.totalNativePeriodFrame K D.ball D.places (FourSplittings.CM.newThetaSigns K v) z.val u)) =
        RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) (C u) := by
  have hframe := CoefficientSourceFrame.CM.exists_source_coefficient_frame K D.ball D.places D.pair.delta D.pair.delta_imaginary
    D.pair.delta_ne_zero (ConcreteApproximationIntrinsicArithmetic.CM.approximationNativeCoefficients K D A) (ConcreteApproximationIntrinsicArithmetic.CM.approximation_native_coefficients_fixed K D A)
    (ConcreteApproximationIntrinsicArithmetic.CM.approximation_native_coefficients_nonzero K D A) (FourSplittings.CM.newThetaSigns K v)
    (ConcreteApproximationIntrinsicArithmetic.CM.approximation_native_active_signs K D hid) (ConcreteApproximationIntrinsicArithmetic.CM.approximation_native_coefficient_signs K D A)
  refine ⟨hframe.choose, ?_⟩
  intro z u
  exact (ConcreteApproximationComplexComponents.CM.approximation_complex_basis_components K D A hid
    (AdaptedTotal.CM.totalNativePeriodFrame K D.ball D.places (FourSplittings.CM.newThetaSigns K v) z.val u)).trans (hframe.choose_spec z u)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationGeometricFrame.CM
