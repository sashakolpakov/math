import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallWedgeDecomposition
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSourceFamilies
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcretePrincipalPersistence

/-! # Concrete Wedge Decomposition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteWedgeDecomposition.CM

noncomputable section

/-! Apply full native ThetaKernel to the actual initial form and every selected
normalized approximation from the fixed original total finite input. -/

open scoped Classical _root_.NumberField _root_.Manifold ContDiff
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.Data OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) (T : InitialSetup.CM.InitialBallTheta K D) (hid : ∀ i, (v i).val 1 = true)

include hid in
theorem actual_initial_theta_wedge_decomposition (hAdelicTheta : RepresentationTheory.Theta.Adelic.Data.CompleteStatement) :
    ∃ (c : ℂ) (n : ℕ) (φ ψ : Fin n → RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K D.places)),
      T.form = ∑ i, c • BallForms.CM.sourceBallTwoForm K (D.initialPeriods 0) (D.initialPeriods 1) (φ i) (ψ i) := by
  obtain ⟨C⟩ := SourceIntrinsicKernel.CM.exists_source_native_c38_data K D.pair (ConcreteApproximationIntrinsicArithmetic.CM.initial_native_active_signs K D hid) hAdelicTheta
  apply BallWedgeDecomposition.CM.ball_top_eq_sum_source_wedges K (FourSplittings.CM.initialThetaSigns K v) D.pair
    (ConcreteApproximationIntrinsicArithmetic.CM.initial_native_active_signs K D hid) C D.initialPeriods D.initial_coefficients T.input 1 T.form T.pure
  intro e z hz
  rw [one_mul]
  exact T.coefficient e.val e.property z hz

include hid in
theorem actual_approximation_theta_wedge_decomposition (hAdelicTheta : RepresentationTheory.Theta.Adelic.Data.CompleteStatement)
    (n : ℕ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2)
    (hpure : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain 2 0 form.val)
    (hcoeff : ∀ (e : OpenPartialHomeomorph D.ball.Domain HeckeCycles.GeometricSource.CM.BallChart), e ∈ atlas HeckeCycles.GeometricSource.CM.BallChart D.ball.Domain →
      ∀ z ∈ D.ball.domain, form.val.inChart e z (Pi.basisFun ℂ (Fin 2)) =
        CompactBallNeighborhood.CM.normalizedSplitThetaCoefficient K D T.input n z) :
    ∃ (c : ℂ) (r : ℕ) (φ ψ : Fin r → RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K D.places)),
      form = ∑ i, c • BallForms.CM.sourceBallTwoForm K ((ApproximationSequence.CM.approximationSequence K D n).periods 0)
        ((ApproximationSequence.CM.approximationSequence K D n).periods 1) (φ i) (ψ i) := by
  let A := ApproximationSequence.CM.approximationSequence K D n
  have hQ := ConcreteLineLagrangianPair.CM.exists_actual_approximation_lagrangian_pair K D A hid
  obtain ⟨C⟩ := SourceIntrinsicKernel.CM.exists_source_native_c38_data K hQ.choose (ConcreteApproximationIntrinsicArithmetic.CM.approximation_native_active_signs K D hid) hAdelicTheta
  apply BallWedgeDecomposition.CM.ball_top_eq_sum_source_wedges K (FourSplittings.CM.newThetaSigns K v) hQ.choose
    (ConcreteApproximationIntrinsicArithmetic.CM.approximation_native_active_signs K D hid) C A.periods hQ.choose_spec.2.2
    (ApproximationCovariance.CM.approximationSplitFiniteInput K D A T.input)
    (SplitCoefficientCovariance.CM.approximationSplitCoefficientFactor K D A 0) form hpure
  intro e z hz
  exact hcoeff e.val e.property z hz

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteWedgeDecomposition.CM
