import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceTensorCotangentProjection

/-! # Concrete Approximation Coefficient Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationCoefficientAction.CM

noncomputable section

/-! At the common principal level the actual split-source theta
coefficient transforms by the inverse determinant of the literal ball
derivative. Both projective denominators cancel in the tensor law. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)
  (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : D.ball.principalLevel N g)
  (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K D.places)) (hcov : ConcreteApproximationLevel.CM.ActualApproximationThetaCovariant K D hid φ N g hg)

include hcov

theorem approximation_source_tangent_tensor_covariant (z : D.ball.Domain)
    (j k : Fin 2) (ξ η : HeckeCycles.GeometricSource.CM.BallChart) :
    ConcreteApproximationFrameAction.CM.sourceAdaptedThetaTensor K A.periods (ApproximationCovariance.CM.approximationSplitFiniteInput K D A φ) 2
      (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)
      ![TotalSourceCotangentAction.CM.totalAdaptedTangentSlot K D.places j (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val ξ),
        TotalSourceCotangentAction.CM.totalAdaptedTangentSlot K D.places k (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val η)] =
      ConcreteApproximationFrameAction.CM.sourceAdaptedThetaTensor K A.periods (ApproximationCovariance.CM.approximationSplitFiniteInput K D A φ) 2 z.val
        ![TotalSourceCotangentAction.CM.totalAdaptedTangentSlot K D.places j ξ, TotalSourceCotangentAction.CM.totalAdaptedTangentSlot K D.places k η] := by
  let S := ConcreteApproximationFrameAction.CM.totalSourceFrameMatrix K g hg.2.1 D.ball D.places (FourSplittings.CM.newThetaSigns K v) z.val
  let κ := (BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2
  let u := ![TotalSourceCotangentAction.CM.totalAdaptedTangentSlot K D.places j ξ, TotalSourceCotangentAction.CM.totalAdaptedTangentSlot K D.places k η]
  let u' := ![TotalSourceCotangentAction.CM.totalAdaptedTangentSlot K D.places j (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val ξ),
    TotalSourceCotangentAction.CM.totalAdaptedTangentSlot K D.places k (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val η)]
  let T := ConcreteApproximationFrameAction.CM.sourceAdaptedThetaTensor K A.periods (ApproximationCovariance.CM.approximationSplitFiniteInput K D A φ) 2
    (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)
  have hu : (fun i : Fin 2 => S⁻¹ᵀ.mulVec (u i)) = fun i => κ • u' i := by
    funext i
    fin_cases i
    · exact TotalSourceCotangentAction.CM.total_source_dual_tangent K g hg.2.1 D.ball D.places (FourSplittings.CM.newThetaSigns K v) hg.1 z j ξ
    · exact TotalSourceCotangentAction.CM.total_source_dual_tangent K g hg.2.1 D.ball D.places (FourSplittings.CM.newThetaSigns K v) hg.1 z k η
  have hs : T (fun i => κ • u' i) = κ ^ 2 * T u' := by
    have h := T.toMultilinearMap.map_smul_univ (fun _ : Fin 2 => κ) u'
    simpa only [Fin.prod_univ_two, smul_eq_mul, ← pow_two] using! h
  have ht := congrArg T hu
  have hn := ConcreteApproximationFrameAction.CM.approximation_source_tensor_covariant K D A hid N g hg φ hcov z 2 u
  exact mul_left_cancel₀ (pow_ne_zero 2 (BallLineAction.CM.ball_action_denominator_ne_zero K D.ball g hg.1 z))
    (hs.symm.trans (ht.symm.trans hn))

theorem approximation_source_coefficient_covariant (z : D.ball.Domain) :
    InitialTensor.CM.splitThetaTopCoefficient K (A.periods 0) (A.periods 1) (ApproximationCovariance.CM.approximationSplitFiniteInput K D A φ)
      (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) * LinearMap.det (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val).toLinearMap =
      InitialTensor.CM.splitThetaTopCoefficient K (A.periods 0) (A.periods 1) (ApproximationCovariance.CM.approximationSplitFiniteInput K D A φ) z.val := by
  have he := congrArg RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (funext (fun a : Fin 2 × Fin 2 => funext (fun b : Fin 2 × Fin 2 =>
    approximation_source_tangent_tensor_covariant K D A hid N g hg φ hcov z a.2 b.2
      ((Pi.basisFun ℂ (Fin 2)) a.1) ((Pi.basisFun ℂ (Fin 2)) b.1))))
  have hd := SourceTensorCotangentProjection.CM.source_tangent_double_alt K A.periods (ApproximationCovariance.CM.approximationSplitFiniteInput K D A φ)
    (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val)
  have h := hd.symm.trans he
  simpa only [SourceTensorCotangentProjection.CM.total_adapted_tangent_basis, SourceTensorCotangentProjection.CM.source_adapted_tensor_slots, InitialTensor.CM.splitThetaTopCoefficient, mul_comm] using! h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationCoefficientAction.CM
