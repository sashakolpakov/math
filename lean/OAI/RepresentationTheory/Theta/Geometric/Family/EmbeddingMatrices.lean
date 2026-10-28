import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.CentralPeriods
import OAI.RepresentationTheory.Theta.Geometric.Family.EmbeddingInclusion
import OAI.RepresentationTheory.Theta.Geometric.Family.NormalizedHodgeLines

/-! # Embedding Matrices -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Restrict the constructed holomorphic period matrix to a fixed
central embedding block. Its kernel is the actual transported Hodge line. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation Family.FieldActions.familyFieldPeriodAction Family.PELCoordinates.familyPELCoordinates
  Intrinsic.CompatibleTransport.NativeCompatibleTransport.normalizedHodgeLine Family.EmbeddingInclusion.familyEmbeddingInclusion MarkingComplexTransport.markingComplexBasis

variable {E : Type} [Field E] [NumberField E] {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left}
    {ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (H : Intrinsic.HolomorphicTransport.NativeHolomorphicTransport A ρ F)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

def Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.embeddingCoefficients (τ : E →ₐ[ℚ] ℂ) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) : Geometry.ComplexBall.PrescribedSignsB.Vec →L[ℂ] (Fin F.rank → ℂ) :=
  ((MarkingComplexTransport.markingComplexBasis H.centralMarking).equivFun.toLinearMap.comp
    ((Family.EmbeddingInclusion.familyEmbeddingInclusion A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree τ).comp
      e₀.toLinearMap)).toContinuousLinearMap

def Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.embeddingMatrix (τ : E →ₐ[ℚ] ℂ) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z : Intrinsic.FamilyFrames.FamilyChartBase C) :
    Geometry.ComplexBall.PrescribedSignsB.Vec →L[ℂ] (Fin H.dimension → ℂ) :=
  (H.matrix z).comp (H.embeddingCoefficients s hs hg hdegree τ e₀)

theorem Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.embeddingMatrix_apply (τ : E →ₐ[ℚ] ℂ) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z : Intrinsic.FamilyFrames.FamilyChartBase C) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    H.embeddingMatrix s hs hg hdegree τ e₀ z v =
      H.matrix z ((MarkingComplexTransport.markingComplexBasis H.centralMarking).equivFun
        (Family.EmbeddingInclusion.familyEmbeddingInclusion A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree τ (e₀ v))) := by
  unfold Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.embeddingMatrix Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.embeddingCoefficients
  change H.matrix z (((MarkingComplexTransport.markingComplexBasis H.centralMarking).equivFun.toLinearMap.comp
    ((Family.EmbeddingInclusion.familyEmbeddingInclusion A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree τ).comp
      e₀.toLinearMap)) v) = _
  rfl

theorem Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.embeddingMatrix_holomorphic (τ : E →ₐ[ℚ] ℂ) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) :
    DifferentiableOn ℂ (H.embeddingMatrix s hs hg hdegree τ e₀) H.compatible.neighborhood := by
  change DifferentiableOn ℂ (fun z => (H.matrix z).comp (H.embeddingCoefficients s hs hg hdegree τ e₀))
    H.compatible.neighborhood
  exact H.holomorphic.clm_comp (differentiableOn_const (H.embeddingCoefficients s hs hg hdegree τ e₀))

attribute [local irreducible] Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.embeddingMatrix Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.embeddingCoefficients

theorem Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.embeddingMatrix_kernel (τ : E →ₐ[ℚ] ℂ) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z : H.compatible.neighborhood) :
    (H.embeddingMatrix s hs hg hdegree τ e₀ z).ker =
      H.compatible.normalizedHodgeLine A ρ s hs hg hdegree τ e₀ z := by
  apply Submodule.ext
  intro v
  change H.embeddingMatrix s hs hg hdegree τ e₀ z v = 0 ↔ _
  rw [H.embeddingMatrix_apply, H.matrix_kernel_iff]
  change AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety
    ((F.nativeRationalTransport z (H.compatible.subset_frame z.property) (H.compatible.subset_chart z.property)
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z))).baseChange ℂ
      (Family.EmbeddingInclusion.familyEmbeddingInclusion A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree τ (e₀ v))) = 0 ↔ _
  rw [H.compatible.embeddingInclusion_transport, Family.EmbeddingInclusion.familyEmbeddingInclusion_kernel]
  unfold Intrinsic.CompatibleTransport.NativeCompatibleTransport.normalizedHodgeLine AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine.NativeHermitianMarking.nativeNormalizedHodgeLine
  rw [Submodule.mem_map_equiv]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric
