import OAI.RepresentationTheory.Theta.DerivativeFactorizationPrerequisites
import OAI.RepresentationTheory.Theta.Factorization
import OAI.RepresentationTheory.Theta.Compatibility

/-! # Derivative Factorization -/

namespace OAI.RepresentationTheory.Theta.DerivativeFactorization.Conditional

noncomputable section

/-!
# DerivativeFactorization, conditional on the committed CompletedTheta and TensorDecomposition inputs

The prerequisite propositions are explicit hypotheses. The committed target
already supplies the uncompleted functional equation as a natural hypothesis;
its completion and first-derivative consequences follow directly from the
Gaussian formulas. CompletedTheta's stronger lattice tensor law is therefore unnecessary.
TensorDecomposition's decomposition of general inputs is unnecessary for the target's pure
tensor inputs, whose local constancy and compact support are proved directly.
No additional substantive assumption is imposed.

The finite-adelic support-to-lattice bridge, absolute convergence, weighted
first-coefficient holomorphicity, block inverse identity, rational covariance,
and trace-coordinate reindexing are all proved in result-specific helpers.
The supplied trace coordinates and bare Weil/Poisson equation remain exactly
the natural hypotheses of the committed target. No statement stub is used.
-/

universe uC uEI uEX uEV uEY

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem first_derivatives_uncorrected_holomorphic
    (_h_C3_4 : DerivativeFactorizationPrerequisites.Prerequisites.Statement)
    (_h_E32 : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement)
    (φ : DerivativeFactorizationDefinitions.Input ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    HasFDerivAt (DerivativeFactorizationDefinitions.theta φ Z.matrix)
      (DerivativeFactorizationDefinitions.firstCoefficient φ Z.matrix) 0 ∧
    HasFDerivAt (DerivativeFactorizationDefinitions.completed φ Z)
      (DerivativeFactorizationDefinitions.firstCoefficient φ Z.matrix) 0 ∧
    fderiv ℂ (DerivativeFactorizationDefinitions.completed φ Z) 0 =
      fderiv ℂ (DerivativeFactorizationDefinitions.theta φ Z.matrix) 0 ∧
    DifferentiableAt ℂ (DerivativeFactorizationDefinitions.firstCoefficient φ) Z.matrix := by
  exact DerivativeFactorizationAdelicLattice.first_derivatives_uncorrected_holomorphic φ Z

theorem direct_sum_factorization
    (_h_C3_4 : DerivativeFactorizationPrerequisites.Prerequisites.Statement)
    (_h_E32 : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement)
    (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix κ)
    (Z₁₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Sum ι κ))
    (hZ : Z₁₂.matrix =
      Matrix.fromBlocks Z₁.matrix 0 0 Z₂.matrix)
    (φ₁ : DerivativeFactorizationDefinitions.Input ι) (φ₂ : DerivativeFactorizationDefinitions.Input κ) :
    ∃ φ₁₂ : DerivativeFactorizationDefinitions.Input (Sum ι κ),
      (∀ a,
        φ₁₂.1 a =
          φ₁.1 (fun i => a (Sum.inl i)) *
          φ₂.1 (fun j => a (Sum.inr j))) ∧
      (∀ z₁ z₂,
        DerivativeFactorizationDefinitions.completed φ₁₂ Z₁₂ (Sum.elim z₁ z₂) =
          DerivativeFactorizationDefinitions.completed φ₁ Z₁ z₁ * DerivativeFactorizationDefinitions.completed φ₂ Z₂ z₂) := by
  exact Factorization.Derivative.direct_sum_factorization Z₁ Z₂ Z₁₂ hZ φ₁ φ₂

theorem rational_adapted_coordinate_change
    (_h_C3_4 : DerivativeFactorizationPrerequisites.Prerequisites.Statement)
    (_h_E32 : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement)
    [DecidableEq ι]
    (gQ : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℚ)
    (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ)
    (hg :
      Matrix.fromBlocks g.A g.B g.C g.D =
        (Matrix.fromBlocks gQ.A gQ.B gQ.C gQ.D).map
          (algebraMap ℚ ℝ))
    (m : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι → ℂ)
    (hm : ∀ Z,
      m Z ^ 2 = (g.complexify.denominator Z.matrix).det)
    (hCompletedTheta : ∀ φ : DerivativeFactorizationDefinitions.Input ι, ∃ φg : DerivativeFactorizationDefinitions.Input ι,
      ∀ (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
        DerivativeFactorizationDefinitions.theta φg (g.transformSiegel Z).matrix
            (g.jacobiChange Z z) =
          m Z * AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (g.thetaCorrectionForm Z) z *
            DerivativeFactorizationDefinitions.theta φ Z.matrix z)
    (φ : DerivativeFactorizationDefinitions.Input ι) :
    ∃ φg : DerivativeFactorizationDefinitions.Input ι, ∀ Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι,
      (∀ z,
        DerivativeFactorizationDefinitions.completed φg (g.transformSiegel Z) (g.jacobiChange Z z) =
          m Z * DerivativeFactorizationDefinitions.completed φ Z z) ∧
      (DerivativeFactorizationDefinitions.firstCoefficient φg (g.transformSiegel Z).matrix).comp
          (g.jacobiChange Z) =
        m Z • DerivativeFactorizationDefinitions.firstCoefficient φ Z.matrix := by
  exact Compatibility.DerivativeFactorization.rational_adapted_coordinate_change gQ g hg m hm hCompletedTheta φ

theorem trace_and_restriction_of_scalars
    (_h_C3_4 : DerivativeFactorizationPrerequisites.Prerequisites.Statement)
    (_h_E32 : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement)
    {F η : Type*}
    [Field F] [NumberField F] [Algebra ℚ F] [Fintype η]
    (e : (η → F) ≃ₗ[ℚ] (ι → ℚ))
    (ef : (η → DerivativeFactorizationDefinitions.AFf F) ≃ₜ (ι → DerivativeFactorizationDefinitions.AQf))
    (hdiag : ∀ x : η → F,
      ef (fun j => algebraMap F (DerivativeFactorizationDefinitions.AFf F) (x j)) =
        DerivativeFactorizationDefinitions.diagonal (e x))
    (TrA : DerivativeFactorizationDefinitions.AF F →+ DerivativeFactorizationDefinitions.AQ)
    (hTrA : ∀ a : F,
      TrA (algebraMap F (DerivativeFactorizationDefinitions.AF F) a) =
        algebraMap ℚ DerivativeFactorizationDefinitions.AQ (Algebra.trace ℚ F a))
    (ψQ : AddChar DerivativeFactorizationDefinitions.AQ ℂ)
    (hψQ : ∀ a : ℚ, ψQ (algebraMap ℚ DerivativeFactorizationDefinitions.AQ a) = 1)
    (φF : DerivativeFactorizationDefinitions.FiniteSchwartz (η → DerivativeFactorizationDefinitions.AFf F))
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    let ψF : DerivativeFactorizationDefinitions.AF F → ℂ := fun a => ψQ (TrA a)
    (∀ a b, ψF (a + b) = ψF a * ψF b) ∧
    (∀ a : F, ψF (algebraMap F (DerivativeFactorizationDefinitions.AF F) a) = 1) ∧
    ∃ φQ : DerivativeFactorizationDefinitions.Input ι,
      (∀ a, φQ.1 a = φF.1 (ef.symm a)) ∧
      (∀ z,
        AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor Z.completionForm z *
          (∑' x : η → F,
            φF.1 (fun j => algebraMap F (DerivativeFactorizationDefinitions.AFf F) (x j)) *
              DerivativeFactorizationDefinitions.kernel Z.matrix (e x) z) =
          DerivativeFactorizationDefinitions.completed φQ Z z) := by
  exact Compatibility.DerivativeFactorization.trace_and_restriction_of_scalars e ef hdiag TrA hTrA ψQ hψQ φF Z

end

end OAI.RepresentationTheory.Theta.DerivativeFactorization.Conditional
