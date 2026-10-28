import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MovingTotalPeriod
import OAI.RepresentationTheory.Theta.CompletionAnalysis
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicAnalysis
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF

/-! # Total Jet Regularity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalJetRegularity.CM

noncomputable section

/-! ThetaCycle: actual completed Jacobi jets vary smoothly with the total period,
while the genuine finite Schwartz input remains fixed. -/

open scoped Classical _root_.Matrix ContDiff _root_.Matrix.Norms.Elementwise BoundedContinuousFunction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem finite_theta_lattice_presentation (φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input ι) :
    ∃ (L : Submodule ℤ (ι → ℝ)) (_ : DiscreteTopology L) (ψ : L →ᵇ ℂ),
      ∀ B z, RepresentationTheory.Theta.DerivativeFactorizationDefinitions.theta φ B z = RepresentationTheory.Theta.Definitions.theta L ψ B z := by
  obtain ⟨L, hL, q, hqi, hq, hsupport⟩ := RepresentationTheory.Theta.Kernel.AdelicSupport.input_lattice_presentation φ
  let : DiscreteTopology L := hL
  obtain ⟨C, hC⟩ := RepresentationTheory.Theta.Kernel.AdelicSupport.input_bounded φ
  let ψ : L →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun x => φ.1 (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.diagonal (q x))) C (fun x => hC _)
  refine ⟨L, hL, ψ, ?_⟩
  intro B z
  have hq' : ∀ x : L, RepresentationTheory.Theta.DerivativeFactorizationDefinitions.realPosition (q x) = (x : ι → ℝ) := hq
  have hterm (x : L) :
      φ.1 (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.diagonal (q x)) * RepresentationTheory.Theta.DerivativeFactorizationDefinitions.kernel B (q x) z =
        RepresentationTheory.Theta.Kernel.Analysis.latticeSummand L ψ x (B, z) := by
    simp only [RepresentationTheory.Theta.DerivativeFactorizationDefinitions.kernel, RepresentationTheory.Theta.Kernel.Analysis.latticeSummand, hq', ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply]
    rfl
  have hzero (r : ι → ℚ) (hr : r ∉ Set.range q) :
      φ.1 (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.diagonal r) * RepresentationTheory.Theta.DerivativeFactorizationDefinitions.kernel B r z = 0 := by
    have hp : φ.1 (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.diagonal r) = 0 := by
      by_contra h
      exact hr (hsupport r h)
    rw [hp, zero_mul]
  have he := hqi.tsum_eq
    (f := fun r => φ.1 (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.diagonal r) * RepresentationTheory.Theta.DerivativeFactorizationDefinitions.kernel B r z)
    (fun r hr => by
      by_contra h
      exact hr (hzero r h))
  simpa only [RepresentationTheory.Theta.DerivativeFactorizationDefinitions.theta, RepresentationTheory.Theta.Definitions.theta, hterm, RepresentationTheory.Theta.Kernel.Analysis.latticeSummand] using he.symm

def finiteCompletedTheta (φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input ι) (B : Matrix ι ι ℂ)
    (z : ι → ℂ) : ℂ :=
  ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (((Real.pi : ℂ) / 2) • ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary B)⁻¹)) z *
    RepresentationTheory.Theta.DerivativeFactorizationDefinitions.theta φ B z

def finiteCompletedJet (φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input ι) (a : ℕ) (B : Matrix ι ι ℂ) :=
  iteratedFDeriv ℂ a (finiteCompletedTheta φ B) 0

theorem finite_completed_theta_eq (φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input ι) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    finiteCompletedTheta φ Z.matrix = RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed φ Z := by
  funext z
  simp only [finiteCompletedTheta, RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed, ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor,
    _root_.smul_apply, smul_eq_mul, Z.completionForm_quadratic, ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear_apply]

/-- The literal unnormalized Jacobi derivative, including the completion
term, is real analytic at every positive Siegel matrix. -/
theorem finite_completed_jet_contDiffAt (φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input ι)
    (a : ℕ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    ContDiffAt ℝ ω (finiteCompletedJet φ a) Z.matrix := by
  obtain ⟨L, hL, ψ, hθ⟩ := finite_theta_lattice_presentation φ
  let : DiscreteTopology L := hL
  have he : finiteCompletedJet φ a = fun B =>
      iteratedFDeriv ℂ a (RepresentationTheory.Theta.Definitions.completedTheta L ψ B) 0 := by
    funext B
    have hf : finiteCompletedTheta φ B = RepresentationTheory.Theta.Definitions.completedTheta L ψ B := by
      funext z
      exact congrArg (fun t => ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor
        (((Real.pi : ℂ) / 2) • ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary B)⁻¹)) z * t) (hθ B z)
    exact congrArg (fun f => iteratedFDeriv ℂ a f 0) hf
  rw [he]
  let W := (ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z.matrix)⁻¹
  have hj : ContDiffAt ℂ ω
      (fun p : Matrix ι ι ℂ × Matrix ι ι ℂ =>
        iteratedFDeriv ℂ a (RepresentationTheory.Theta.CompletionAnalysis.auxiliaryTheta L ψ p) 0) (Z.matrix, W) :=
    (RepresentationTheory.Theta.Definitions.partial_iteratedFDeriv_contDiffAt
      (RepresentationTheory.Theta.CompletionAnalysis.auxiliaryTheta_contDiffAt L ψ Z W 0) a).comp (Z.matrix, W)
        (contDiffAt_id.prodMk contDiffAt_const)
  have hc : ContDiffAt ℝ ω
      (fun B : Matrix ι ι ℂ => (B, (ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary B)⁻¹)) Z.matrix :=
    contDiffAt_id.prodMk (RepresentationTheory.Theta.Definitions.inverse_imaginary_contDiffAt Z)
  exact (hj.restrict_scalars ℝ).comp Z.matrix hc

theorem finite_completed_jet_smooth_period
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {s : Set V} (hs : IsOpen s) (Z : V → ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (hZ : DifferentiableOn ℂ (fun z => (Z z).matrix) s)
    (φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input ι) (a : ℕ) :
    ContDiffOn ℝ ∞ (fun z => iteratedFDeriv ℂ a (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed φ (Z z)) 0) s := by
  have he : (fun z => iteratedFDeriv ℂ a (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed φ (Z z)) 0) =
      fun z => finiteCompletedJet φ a (Z z).matrix := by
    funext z
    unfold finiteCompletedJet
    rw [finite_completed_theta_eq]
  rw [he]
  have hz := (Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_infty_of_differentiableOn
    hs hZ).restrict_scalars ℝ
  intro z hzs
  exact ((finite_completed_jet_contDiffAt φ a (Z z)).of_le (by simp)).comp_contDiffWithinAt
    z (hz z hzs)

theorem approximation_total_jet_smooth
    (K : IntermediateField ℚ ℂ) [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
    {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
    (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
    (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
    (Φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input (PeriodTotal.CM.TotalPositions K D.places)) (a : ℕ) :
    ContDiffOn ℝ ∞ (fun z => iteratedFDeriv ℂ a
      (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (MovingTotalPeriod.CM.approximationTotalPeriod K D A z)) 0) D.ball.domain :=
  finite_completed_jet_smooth_period D.ball.domain_isOpen _
    (MovingTotalPeriod.CM.approximation_total_period_holomorphic K D A) Φ a

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalJetRegularity.CM
