import OAI.RepresentationTheory.Theta.Geometric.Universal.BallPeriods
import OAI.RepresentationTheory.Theta.Geometric.Universal.DistinguishedRank
import OAI.RepresentationTheory.Theta.Geometric.Relative.MarkedTransport

/-! # Hodge Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric.Universal.HodgeComparison

noncomputable section

/-! Equal local distinguished period kernels in the actual universal
family give its full original rational Hodge comparison. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ D.complexSpace) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)

theorem complexUniversal_isHodgeMap_of_kernel_eq (hs : 0 < s)
    (hdegree : Module.finrank ℚ E = 2 * s) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (z w : (HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x).compatible.neighborhood)
    (heq : ((HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x).embeddingMatrix s hs rfl hdegree
      (D.reference.embeddings D.reference.distinguished) e₀ z).ker =
      ((HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x).embeddingMatrix s hs rfl hdegree
        (D.reference.embeddings D.reference.distinguished) e₀ w).ker) :
    let A := PELConditions.complexUniversalPolarized D hg f
    let ρ := PELConditions.complexUniversalAction D hg f
    let C := FamilyPeriodCharts.complexUniversalFamilyCharts D f x
    let H := HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap (AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety)
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)).variety)
      (H.compatible.rationalBetween A ρ z w).toLinearMap := by
  let A := PELConditions.complexUniversalPolarized D hg f
  let ρ := PELConditions.complexUniversalAction D hg f
  let C := FamilyPeriodCharts.complexUniversalFamilyCharts D f x
  let H := HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x
  have hline := (H.embeddingMatrix_kernel s hs rfl hdegree
    (D.reference.embeddings D.reference.distinguished) e₀ z).symm.trans
      (heq.trans (H.embeddingMatrix_kernel s hs rfl hdegree
        (D.reference.embeddings D.reference.distinguished) e₀ w))
  have hH := H.compatible.markedBetween_isHodgeMap A ρ s hs rfl hdegree
    (PELConditions.complexUniversal_rosati D hg f) (Reference.BallSigns.referencePositiveImaginaryScalar D.reference)
    (Reference.BallSigns.referencePositiveImaginaryScalar_spec D.reference hg.reference_admissible).1
    D.reference.embeddings D.reference.distinguished hg.reference_admissible.1.2 e₀ z w hline
    (fun i hi => ⟨D.reference.firstLieRank i, by
      unfold AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.firstLieRank
      rw [ite_eq_right hi]
      split <;> simp,
      DistinguishedRank.complexUniversal_embedding_rank D hg f (Intrinsic.FamilyFrames.familyChartParameter C z) i,
      DistinguishedRank.complexUniversal_embedding_rank D hg f (Intrinsic.FamilyFrames.familyChartParameter C w) i⟩)
  rw [H.compatible.markedBetween_eq_rationalBetween A ρ s hs rfl hdegree z w] at hH
  exact hH

end

end OAI.RepresentationTheory.Theta.Geometric.Universal.HodgeComparison
