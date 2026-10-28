import OAI.RepresentationTheory.Theta.Geometric.Family.CentralNormalizer
import OAI.RepresentationTheory.Theta.Geometric.Family.EmbeddingMatrices
import OAI.RepresentationTheory.Theta.Geometric.Normalized.KernelCoordinates

/-! # Holomorphic Ball Periods -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Construct local holomorphic negative-ball coordinates of the actual
PEL family, retaining its common polarization, field, and full-level frame. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

attribute [local irreducible] Family.HermitianTransport.familyHermitianMatrix Intrinsic.CompatibleTransport.NativeCompatibleTransport.normalizedHodgeLine
  Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.embeddingMatrix

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left}
    {ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (H : Intrinsic.HolomorphicTransport.NativeHolomorphicTransport A ρ F)

theorem Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.exists_holomorphic_ball_periods (hρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (ξ : E) (hξ : ξ ≠ 0) (hconj : AlgebraicGeometry.ComplexMultiplication.CM.TraceForm.cmFieldConjugation E ξ = -ξ)
    (τ : E →ₐ[ℚ] ℂ) (him : 0 < (τ ξ).im) (b : E)
    (hb : AlgebraicGeometry.ComplexMultiplication.CM.TraceForm.cmFieldConjugation E b = b) (hbneg : (τ b).re < 0)
    (hr : ∀ z : H.compatible.neighborhood,
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
        (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
        (τ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) 2) :
    ∃ (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (O : Set (Intrinsic.FamilyFrames.FamilyChartBase C)) (period : Intrinsic.FamilyFrames.FamilyChartBase C → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      IsOpen O ∧ Intrinsic.FamilyFrames.familyChartCenter C ∈ O ∧ O ⊆ H.compatible.neighborhood ∧
      (∀ v w, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm
        ((Family.HermitianTransport.familyHermitianMatrix A ρ hρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree ξ).map τ)
        (e₀ v) (e₀ w) = AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, τ b]) v w) ∧
      DifferentiableOn ℂ period O ∧ ∀ z ∈ O,
        (H.embeddingMatrix s hs hg hdegree τ e₀ z).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector (period z)} ∧
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, τ b])
          (Geometry.ComplexBall.PrescribedSignsB.lineVector (period z)) (Geometry.ComplexBall.PrescribedSignsB.lineVector (period z))).re < 0 := by
  obtain ⟨e₀, he₀⟩ := Family.CentralNormalizer.exists_familyHermitian_normalizer A ρ hρ
    (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree ξ hξ hconj τ him b hb hbneg
    (hr ⟨Intrinsic.FamilyFrames.familyChartCenter C, H.compatible.center⟩)
  have hline (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ H.compatible.neighborhood) :
      ∃ w : Geometry.ComplexBall.PrescribedSignsB.BallChart, (H.embeddingMatrix s hs hg hdegree τ e₀ z).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w} := by
    obtain ⟨w, hw, _⟩ := H.compatible.exists_normalizedHodge_ball_coordinate
      A ρ s hs hg hdegree hρ ξ hξ hconj τ him b e₀ he₀ ⟨z, hz⟩ (hr ⟨z, hz⟩)
    exact ⟨w, (H.embeddingMatrix_kernel s hs hg hdegree τ e₀ ⟨z, hz⟩).trans hw.1⟩
  obtain ⟨O, period, hO, hxO, hOU, hhol, hker⟩ := Normalized.KernelCoordinates.exists_holomorphic_normalized_kernel_coordinate
    (H.embeddingMatrix s hs hg hdegree τ e₀) H.compatible.neighborhood H.compatible.isOpen
    (H.embeddingMatrix_holomorphic s hs hg hdegree τ e₀) (Intrinsic.FamilyFrames.familyChartCenter C) H.compatible.center hline
  refine ⟨e₀, O, period, hO, hxO, hOU, he₀, hhol, ?_⟩
  intro z hz
  obtain ⟨w, hw, _⟩ := H.compatible.exists_normalizedHodge_ball_coordinate
    A ρ s hs hg hdegree hρ ξ hξ hconj τ him b e₀ he₀ ⟨z, hOU hz⟩ (hr ⟨z, hOU hz⟩)
  have heq : period z = w := AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine.lineVector_span_injective
    ((hker z hz).symm.trans ((H.embeddingMatrix_kernel s hs hg hdegree τ e₀ ⟨z, hOU hz⟩).trans hw.1))
  exact ⟨hker z hz, by simpa only [heq] using hw.2⟩

end

end OAI.RepresentationTheory.Theta.Geometric
