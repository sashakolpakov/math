import OAI.Geometry.ComplexBall.CotangentBundle
import OAI.RepresentationTheory.Theta.DerivativeFactorization

/-! # Intrinsic Prerequisites -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicPrerequisites.Intrinsic

noncomputable section

/-! Complete prerequisite propositions for native ThetaKernel. CotangentBundle retains
every bundle-calculus input and all three conclusions. DerivativeFactorization retains its
full CompletedTheta and TensorDecomposition inputs and all four clauses, including the original bare
functional-equation and trace-coordinate premises. -/

universe uB uA uI uK uF uEta uC uEI uEX uEV uEY

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

def CotangentBundleStatement : Prop :=
  ∀ {B : Type uB} {A : Type uA} [CommSemiring B] [CommGroup A]
    (C : Geometry.ComplexBall.CotangentBundle.BundleCalculus B A) (n : ℕ) (L : A) (Vμ Q P K ℱ : B),
    C.rank Vμ = 3 → C.rank P = n → C.shortExact (C.line L) Vμ Q →
    C.det Vμ = 1 → C.det P = 1 → C.det K = 1 →
    ℱ = C.line L * P + C.dual Q * C.dual P + K →
    C.det ℱ = L ^ (2 * n) ∧
    (∃ H : A, H = L ^ n ∧ H ^ 2 = C.det ℱ) ∧
    Geometry.ComplexBall.CotangentBundle.projectiveCotangent C L Q = C.line L * C.dual Q

theorem full_CotangentBundle : CotangentBundleStatement :=
  Geometry.ComplexBall.CotangentBundle.determinant_and_cotangent_identities

def DerivativeFactorizationStatement : Prop :=
  ∀ (_h_C3_4 : DerivativeFactorizationPrerequisites.Prerequisites.Statement.{uC})
    (_h_E32 : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{uEI, uEX, uEV, uEY})
    {ι : Type uI} {κ : Type uK} [Fintype ι] [Fintype κ],
    (∀ (φ : DerivativeFactorizationDefinitions.Input ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι),
      HasFDerivAt (DerivativeFactorizationDefinitions.theta φ Z.matrix) (DerivativeFactorizationDefinitions.firstCoefficient φ Z.matrix) 0 ∧
      HasFDerivAt (DerivativeFactorizationDefinitions.completed φ Z) (DerivativeFactorizationDefinitions.firstCoefficient φ Z.matrix) 0 ∧
      fderiv ℂ (DerivativeFactorizationDefinitions.completed φ Z) 0 = fderiv ℂ (DerivativeFactorizationDefinitions.theta φ Z.matrix) 0 ∧
      DifferentiableAt ℂ (DerivativeFactorizationDefinitions.firstCoefficient φ) Z.matrix) ∧
    (∀ (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix κ) (Z₁₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Sum ι κ)),
      Z₁₂.matrix = Matrix.fromBlocks Z₁.matrix 0 0 Z₂.matrix →
      ∀ (φ₁ : DerivativeFactorizationDefinitions.Input ι) (φ₂ : DerivativeFactorizationDefinitions.Input κ), ∃ φ₁₂ : DerivativeFactorizationDefinitions.Input (Sum ι κ),
        (∀ a, φ₁₂.1 a = φ₁.1 (fun i => a (.inl i)) * φ₂.1 (fun j => a (.inr j))) ∧
        ∀ z₁ z₂, DerivativeFactorizationDefinitions.completed φ₁₂ Z₁₂ (Sum.elim z₁ z₂) = DerivativeFactorizationDefinitions.completed φ₁ Z₁ z₁ * DerivativeFactorizationDefinitions.completed φ₂ Z₂ z₂) ∧
    (∀ [DecidableEq ι] (gQ : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℚ) (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ),
      Matrix.fromBlocks g.A g.B g.C g.D =
        (Matrix.fromBlocks gQ.A gQ.B gQ.C gQ.D).map (algebraMap ℚ ℝ) →
      ∀ (m : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι → ℂ),
        (∀ Z, m Z ^ 2 = (g.complexify.denominator Z.matrix).det) →
        (∀ φ : DerivativeFactorizationDefinitions.Input ι, ∃ φg : DerivativeFactorizationDefinitions.Input ι, ∀ (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
          DerivativeFactorizationDefinitions.theta φg (g.transformSiegel Z).matrix (g.jacobiChange Z z) =
            m Z * AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (g.thetaCorrectionForm Z) z * DerivativeFactorizationDefinitions.theta φ Z.matrix z) →
        ∀ φ : DerivativeFactorizationDefinitions.Input ι, ∃ φg : DerivativeFactorizationDefinitions.Input ι, ∀ Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι,
          (∀ z, DerivativeFactorizationDefinitions.completed φg (g.transformSiegel Z) (g.jacobiChange Z z) = m Z * DerivativeFactorizationDefinitions.completed φ Z z) ∧
          (DerivativeFactorizationDefinitions.firstCoefficient φg (g.transformSiegel Z).matrix).comp (g.jacobiChange Z) =
            m Z • DerivativeFactorizationDefinitions.firstCoefficient φ Z.matrix) ∧
    (∀ {F : Type uF} {η : Type uEta} [Field F] [NumberField F] [Algebra ℚ F] [Fintype η]
      (e : (η → F) ≃ₗ[ℚ] (ι → ℚ)) (ef : (η → DerivativeFactorizationDefinitions.AFf F) ≃ₜ (ι → DerivativeFactorizationDefinitions.AQf)),
      (∀ x : η → F, ef (fun j => algebraMap F (DerivativeFactorizationDefinitions.AFf F) (x j)) = DerivativeFactorizationDefinitions.diagonal (e x)) →
      ∀ (TrA : DerivativeFactorizationDefinitions.AF F →+ DerivativeFactorizationDefinitions.AQ),
        (∀ a : F, TrA (algebraMap F (DerivativeFactorizationDefinitions.AF F) a) = algebraMap ℚ DerivativeFactorizationDefinitions.AQ (Algebra.trace ℚ F a)) →
      ∀ (ψQ : AddChar DerivativeFactorizationDefinitions.AQ ℂ), (∀ a : ℚ, ψQ (algebraMap ℚ DerivativeFactorizationDefinitions.AQ a) = 1) →
      ∀ (φF : DerivativeFactorizationDefinitions.FiniteSchwartz (η → DerivativeFactorizationDefinitions.AFf F)) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι),
        let ψF : DerivativeFactorizationDefinitions.AF F → ℂ := fun a => ψQ (TrA a)
        (∀ a b, ψF (a + b) = ψF a * ψF b) ∧
        (∀ a : F, ψF (algebraMap F (DerivativeFactorizationDefinitions.AF F) a) = 1) ∧
        ∃ φQ : DerivativeFactorizationDefinitions.Input ι, (∀ a, φQ.1 a = φF.1 (ef.symm a)) ∧
          ∀ z, AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor Z.completionForm z *
            (∑' x : η → F, φF.1 (fun j => algebraMap F (DerivativeFactorizationDefinitions.AFf F) (x j)) * DerivativeFactorizationDefinitions.kernel Z.matrix (e x) z) =
              DerivativeFactorizationDefinitions.completed φQ Z z)

theorem full_DerivativeFactorization : DerivativeFactorizationStatement := by
  intro hC hE ι κ _ _
  refine ⟨DerivativeFactorization.Conditional.first_derivatives_uncorrected_holomorphic hC hE,
    DerivativeFactorization.Conditional.direct_sum_factorization hC hE,?_,?_⟩
  · intro _
    exact DerivativeFactorization.Conditional.rational_adapted_coordinate_change hC hE
  · exact DerivativeFactorization.Conditional.trace_and_restriction_of_scalars hC hE

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicPrerequisites.Intrinsic
