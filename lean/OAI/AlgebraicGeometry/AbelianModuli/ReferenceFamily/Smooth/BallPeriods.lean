import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.HolomorphicBallPeriods

/-! # Ball Periods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.BallPeriods

noncomputable section

/-! A smooth actual PEL family constructs its native holomorphic ball
periods, including all charts and compatible integral markings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

theorem exists_smooth_family_ball_periods (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hN : 0 < N) (hρ : ActionData.RosatiConjugation A ρ)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (ξ : E) (hξ : ξ ≠ 0) (hconj : ComplexMultiplication.CM.TraceForm.cmFieldConjugation E ξ = -ξ)
    (τ : E →ₐ[ℚ] ℂ) (him : 0 < (τ ξ).im) (b : E)
    (hb : ComplexMultiplication.CM.TraceForm.cmFieldConjugation E b = b) (hbneg : (τ b).re < 0)
    (hr : ∀ y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S,
      LieRanks.HasLieRank (A.abelian.pullback y.left) (ρ.pullback y.left)
        (τ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) 2) :
    ∃ (C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x) (F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)
      (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport A ρ F)
      (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (O : Set (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C)) (period : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      IsOpen O ∧ RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C ∈ O ∧ O ⊆ H.compatible.neighborhood ∧
      (∀ v w, Complex.HermitianMatrixForm.complexHermitianMatrixForm
        ((RepresentationTheory.Theta.Geometric.Family.HermitianTransport.familyHermitianMatrix A ρ hρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree ξ).map τ)
        (e₀ v) (e₀ w) = Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, τ b]) v w) ∧
      DifferentiableOn ℂ period O ∧ ∀ z ∈ O,
        (H.embeddingMatrix s hs hg hdegree τ e₀ z).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector (period z)} ∧
        (Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, τ b])
          (Geometry.ComplexBall.PrescribedSignsB.lineVector (period z)) (Geometry.ComplexBall.PrescribedSignsB.lineVector (period z))).re < 0 := by
  obtain ⟨C, F, ⟨H⟩⟩ := Intrinsic.HolomorphicTransport.exists_native_family_holomorphic_transport A ρ x hN
  refine ⟨C, F, H, ?_⟩
  exact H.exists_holomorphic_ball_periods hρ s hs hg hdegree ξ hξ hconj τ him b hb hbneg
    (fun z => hr (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.BallPeriods
