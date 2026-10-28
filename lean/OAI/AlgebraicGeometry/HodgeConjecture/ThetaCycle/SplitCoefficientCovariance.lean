import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.GraphSlotTransition
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.DoubleAltBasis
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ApproximationCoefficient

/-! # Split Coefficient Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SplitCoefficientCovariance.CM

noncomputable section

/-! ThetaCycle: the converging original-coordinate Hessian is the actual split
theta top coefficient, with its exact nonzero scalar factors retained. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (Φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input (PeriodTotal.CM.TotalPositions K D.places))

theorem approximation_double_alt_covariance (z : HeckeCycles.GeometricSource.CM.BallChart) :
    (GraphSlotTransition.CM.approximationMultiplicityMatrix K D A).det *
      RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (fun a b => iteratedFDeriv ℂ 2
        (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed (ApproximationCovariance.CM.approximationSplitFiniteInput K D A Φ)
          (BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z))) 0
        ![InitialTensor.CM.splitThetaSlot K (A.periods 0) (A.periods 1) z a,
          InitialTensor.CM.splitThetaSlot K (A.periods 0) (A.periods 1) z b]) =
    ApproximationCovariance.CM.approximationThetaMultiplier K D A z *
      RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (fun a b => iteratedFDeriv ℂ 2
        (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (MovingTotalPeriod.CM.approximationTotalPeriod K D A z)) 0
        ![TotalGraphSlots.CM.totalGraphSlot K (fun i => (D.initialPeriods i).coordinates)
            (MovingTotalPeriod.CM.approximationTotalPeriod K D A z).matrix a,
          TotalGraphSlots.CM.totalGraphSlot K (fun i => (D.initialPeriods i).coordinates)
            (MovingTotalPeriod.CM.approximationTotalPeriod K D A z).matrix b]) := by
  rw [← DoubleAltBasis.CM.double_alt_basis_hessian, ← DoubleAltBasis.CM.double_alt_scalar]
  apply congrArg RepresentationTheory.Theta.Kernel.Calculus.doubleAlt
  funext a b
  rw [← GraphSlotTransition.CM.approximation_graph_slot_transition K D A z a,
    ← GraphSlotTransition.CM.approximation_graph_slot_transition K D A z b]
  have h := ApproximationCovariance.CM.approximation_completed_jet_covariance K D A Φ z 2
    ![TotalGraphSlots.CM.totalGraphSlot K (fun i => (D.initialPeriods i).coordinates)
        (MovingTotalPeriod.CM.approximationTotalPeriod K D A z).matrix a,
      TotalGraphSlots.CM.totalGraphSlot K (fun i => (D.initialPeriods i).coordinates)
        (MovingTotalPeriod.CM.approximationTotalPeriod K D A z).matrix b]
  convert h using 1
  congr 1
  ext i
  fin_cases i <;> rfl

def approximationSplitCoefficientFactor (z : HeckeCycles.GeometricSource.CM.BallChart) : ℂ :=
  ParameterHalfDet.CM.parameterHalfDet K D (ApproximationSequence.CM.newCompactPeriods K D A, z) * (GraphSlotTransition.CM.approximationMultiplicityMatrix K D A).det /
    (ApproximationCovariance.CM.approximationThetaMultiplier K D A z *
      ((A.periods 0).halfDet z : ℂ) * ((A.periods 1).halfDet z : ℂ))

theorem approximation_split_coefficient_covariance (z : HeckeCycles.GeometricSource.CM.BallChart) :
    ApproximationCoefficient.CM.approximationProjectedCoefficient K D Φ A z =
      approximationSplitCoefficientFactor K D A z *
        InitialTensor.CM.splitThetaTopCoefficient K (A.periods 0) (A.periods 1)
          (ApproximationCovariance.CM.approximationSplitFiniteInput K D A Φ) z := by
  have h := approximation_double_alt_covariance K D A Φ z
  unfold ApproximationCoefficient.CM.approximationProjectedCoefficient InitialTensor.CM.splitThetaTopCoefficient InitialTensor.CM.splitThetaTensor
  rw [DoubleAltBasis.CM.double_alt_scalar, DoubleAltBasis.CM.double_alt_scalar]
  unfold approximationSplitCoefficientFactor
  calc
    _ = (ParameterHalfDet.CM.parameterHalfDet K D (ApproximationSequence.CM.newCompactPeriods K D A, z) / ApproximationCovariance.CM.approximationThetaMultiplier K D A z) *
        (ApproximationCovariance.CM.approximationThetaMultiplier K D A z *
          RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (fun a b => iteratedFDeriv ℂ 2
            (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (MovingTotalPeriod.CM.approximationTotalPeriod K D A z)) 0
            ![TotalGraphSlots.CM.totalGraphSlot K (fun i => (D.initialPeriods i).coordinates)
                (MovingTotalPeriod.CM.approximationTotalPeriod K D A z).matrix a,
              TotalGraphSlots.CM.totalGraphSlot K (fun i => (D.initialPeriods i).coordinates)
                (MovingTotalPeriod.CM.approximationTotalPeriod K D A z).matrix b])) := by
      field_simp [ApproximationCovariance.CM.approximation_theta_multiplier_ne_zero K D A z]
    _ = _ := by
      rw [← h]
      field_simp [ApproximationCovariance.CM.approximation_theta_multiplier_ne_zero K D A z, Units.ne_zero]

theorem approximation_split_coefficient_nonzero (z : HeckeCycles.GeometricSource.CM.BallChart)
    (h : ApproximationCoefficient.CM.approximationProjectedCoefficient K D Φ A z ≠ 0) :
    InitialTensor.CM.splitThetaTopCoefficient K (A.periods 0) (A.periods 1)
      (ApproximationCovariance.CM.approximationSplitFiniteInput K D A Φ) z ≠ 0 := by
  rw [approximation_split_coefficient_covariance] at h
  exact (mul_ne_zero_iff.mp h).2

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SplitCoefficientCovariance.CM
