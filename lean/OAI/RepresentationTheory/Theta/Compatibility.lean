import OAI.RepresentationTheory.Theta.DerivativeFactorizationAdelicLattice

/-! # Compatibility -/

namespace OAI.RepresentationTheory.Theta.Compatibility.DerivativeFactorization

noncomputable section

/-! Rational symplectic covariance and trace-coordinate reindexing. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι]

theorem rational_adapted_coordinate_change
    [DecidableEq ι]
    (gQ : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℚ) (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ)
    (_hg : Matrix.fromBlocks g.A g.B g.C g.D =
      (Matrix.fromBlocks gQ.A gQ.B gQ.C gQ.D).map (algebraMap ℚ ℝ))
    (m : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι → ℂ)
    (_hm : ∀ Z, m Z ^ 2 = (g.complexify.denominator Z.matrix).det)
    (hCompletedTheta : ∀ φ : DerivativeFactorizationDefinitions.Input ι, ∃ φg : DerivativeFactorizationDefinitions.Input ι,
      ∀ (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
        DerivativeFactorizationDefinitions.theta φg (g.transformSiegel Z).matrix (g.jacobiChange Z z) =
          m Z * AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (g.thetaCorrectionForm Z) z * DerivativeFactorizationDefinitions.theta φ Z.matrix z)
    (φ : DerivativeFactorizationDefinitions.Input ι) :
    ∃ φg : DerivativeFactorizationDefinitions.Input ι, ∀ Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι,
      (∀ z, DerivativeFactorizationDefinitions.completed φg (g.transformSiegel Z) (g.jacobiChange Z z) =
        m Z * DerivativeFactorizationDefinitions.completed φ Z z) ∧
      (DerivativeFactorizationDefinitions.firstCoefficient φg (g.transformSiegel Z).matrix).comp (g.jacobiChange Z) =
        m Z • DerivativeFactorizationDefinitions.firstCoefficient φ Z.matrix := by
  obtain ⟨φg, hφg⟩ := hCompletedTheta φ
  refine ⟨φg, fun Z => ⟨?_, ?_⟩⟩
  · exact AlgebraicGeometry.ComplexMultiplication.ThetaCovariance.CM.theta_completion_covariance (g.jacobiChange Z) Z.completionForm
      (g.transformSiegel Z).completionForm (g.thetaCorrectionForm Z) (m Z)
      (DerivativeFactorizationDefinitions.theta φ Z.matrix) (DerivativeFactorizationDefinitions.theta φg (g.transformSiegel Z).matrix)
      (fun z => by simpa only [mul_assoc] using hφg Z z)
      (g.completion_correction_identity Z)
  · exact AlgebraicGeometry.ComplexMultiplication.ThetaCovariance.CM.theta_first_derivative_covariance (g.jacobiChange Z)
      (g.thetaCorrectionForm Z) (m Z) (DerivativeFactorizationAdelicLattice.theta_hasFDerivAt_zero φ Z)
      (DerivativeFactorizationAdelicLattice.theta_hasFDerivAt_zero φg (g.transformSiegel Z))
      (fun z => by simpa only [mul_assoc] using hφg Z z)

theorem trace_and_restriction_of_scalars
    {F η : Type*}
    [Field F] [NumberField F] [Algebra ℚ F] [Fintype η]
    (e : (η → F) ≃ₗ[ℚ] (ι → ℚ))
    (ef : (η → DerivativeFactorizationDefinitions.AFf F) ≃ₜ (ι → DerivativeFactorizationDefinitions.AQf))
    (hdiag : ∀ x : η → F,
      ef (fun j => algebraMap F (DerivativeFactorizationDefinitions.AFf F) (x j)) = DerivativeFactorizationDefinitions.diagonal (e x))
    (TrA : DerivativeFactorizationDefinitions.AF F →+ DerivativeFactorizationDefinitions.AQ)
    (hTrA : ∀ a : F, TrA (algebraMap F (DerivativeFactorizationDefinitions.AF F) a) =
      algebraMap ℚ DerivativeFactorizationDefinitions.AQ (Algebra.trace ℚ F a))
    (ψQ : AddChar DerivativeFactorizationDefinitions.AQ ℂ)
    (hψQ : ∀ a : ℚ, ψQ (algebraMap ℚ DerivativeFactorizationDefinitions.AQ a) = 1)
    (φF : DerivativeFactorizationDefinitions.FiniteSchwartz (η → DerivativeFactorizationDefinitions.AFf F)) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    let ψF : DerivativeFactorizationDefinitions.AF F → ℂ := fun a => ψQ (TrA a)
    (∀ a b, ψF (a + b) = ψF a * ψF b) ∧
    (∀ a : F, ψF (algebraMap F (DerivativeFactorizationDefinitions.AF F) a) = 1) ∧
    ∃ φQ : DerivativeFactorizationDefinitions.Input ι,
      (∀ a, φQ.1 a = φF.1 (ef.symm a)) ∧
      (∀ z, AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor Z.completionForm z *
        (∑' x : η → F,
          φF.1 (fun j => algebraMap F (DerivativeFactorizationDefinitions.AFf F) (x j)) * DerivativeFactorizationDefinitions.kernel Z.matrix (e x) z) =
        DerivativeFactorizationDefinitions.completed φQ Z z) := by
  dsimp only
  refine ⟨fun a b => ?_, fun a => ?_, ?_⟩
  · rw [map_add, ψQ.map_add_eq_mul]
  · rw [hTrA, hψQ]
  · let φQ : DerivativeFactorizationDefinitions.Input ι := ⟨φF.1 ∘ ef.symm,
      φF.2.1.comp_continuous ef.symm.continuous,
      φF.2.2.comp_homeomorph ef.symm⟩
    refine ⟨φQ, fun _ => rfl, fun z => ?_⟩
    unfold DerivativeFactorizationDefinitions.completed DerivativeFactorizationDefinitions.theta
    congr 1
    rw [← e.toEquiv.tsum_eq]
    apply tsum_congr
    intro x
    change φF.1 (fun j => algebraMap F (DerivativeFactorizationDefinitions.AFf F) (x j)) * DerivativeFactorizationDefinitions.kernel Z.matrix (e x) z =
      φF.1 (ef.symm (DerivativeFactorizationDefinitions.diagonal (e x))) * DerivativeFactorizationDefinitions.kernel Z.matrix (e x) z
    rw [← hdiag, ef.symm_apply_apply]

end

end OAI.RepresentationTheory.Theta.Compatibility.DerivativeFactorization
