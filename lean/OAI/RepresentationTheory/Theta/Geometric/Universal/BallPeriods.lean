import OAI.RepresentationTheory.Theta.Geometric.Universal.HolomorphicTransport
import OAI.RepresentationTheory.Theta.Geometric.Universal.DistinguishedRank
import OAI.RepresentationTheory.Theta.Geometric.Reference.BallSigns
import OAI.RepresentationTheory.Theta.Geometric.Family.HolomorphicBallPeriods

/-! # Ball Periods -/

namespace OAI.RepresentationTheory.Theta.Geometric.Universal.BallPeriods

noncomputable section

/-! Local holomorphic periods of the actual original universal family
land in the literal reference ball and have its exact native Hodge line. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ D.complexSpace) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)

theorem exists_complexUniversal_ball_periods (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    let C := FamilyPeriodCharts.complexUniversalFamilyCharts D f x
    let H := HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x
    let A := PELConditions.complexUniversalPolarized D hg f
    let ρ := PELConditions.complexUniversalAction D hg f
    ∃ (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (O : Set (Intrinsic.FamilyFrames.FamilyChartBase C)) (period : Intrinsic.FamilyFrames.FamilyChartBase C → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      IsOpen O ∧ Intrinsic.FamilyFrames.familyChartCenter C ∈ O ∧ O ⊆ H.compatible.neighborhood ∧
      (∀ v w, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm
        ((Family.HermitianTransport.familyHermitianMatrix A ρ (PELConditions.complexUniversal_rosati D hg f)
          (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs rfl hdegree
          (Reference.BallSigns.referencePositiveImaginaryScalar D.reference)).map (D.reference.embeddings D.reference.distinguished))
        (e₀ v) (e₀ w) = AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, D.reference.μ D.reference.b]) v w) ∧
      DifferentiableOn ℂ period O ∧ ∀ z ∈ O,
        period z ∈ D.reference.domain ∧
        (H.embeddingMatrix s hs rfl hdegree (D.reference.embeddings D.reference.distinguished) e₀ z).ker =
          Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector (period z)} := by
  let C := FamilyPeriodCharts.complexUniversalFamilyCharts D f x
  let H := HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x
  obtain ⟨hξ, hc, hi⟩ := Reference.BallSigns.referencePositiveImaginaryScalar_spec D.reference hg.reference_admissible
  obtain ⟨e₀, O, period, hO, hxO, hsub, he₀, hhol, hpoint⟩ :=
    H.exists_holomorphic_ball_periods (PELConditions.complexUniversal_rosati D hg f) s hs rfl hdegree
      (Reference.BallSigns.referencePositiveImaginaryScalar D.reference) hξ hc
      (D.reference.embeddings D.reference.distinguished) hi D.reference.b
      hg.reference_admissible.2.1 hg.reference_admissible.2.2.2.1
      (fun z => DistinguishedRank.complexUniversal_distinguished_rank D hg f (Intrinsic.FamilyFrames.familyChartParameter C z))
  exact ⟨e₀, O, period, hO, hxO, hsub, he₀, hhol, fun z hz =>
    ⟨(Reference.BallSigns.reference_ball_diagonal D.reference (period z)).mpr (hpoint z hz).2, (hpoint z hz).1⟩⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Universal.BallPeriods
