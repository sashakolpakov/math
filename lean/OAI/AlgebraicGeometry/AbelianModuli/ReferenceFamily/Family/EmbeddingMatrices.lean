import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CentralPeriods
import OAI.RepresentationTheory.Theta.Geometric.Family.EmbeddingInclusion
import OAI.RepresentationTheory.Theta.Geometric.Family.NormalizedHodgeLines

/-! # Embedding Matrices -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Restrict the constructed holomorphic period matrix to a fixed
central embedding block. Its kernel is the actual transported Hodge line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

attribute [local irreducible] RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation RepresentationTheory.Theta.Geometric.Family.FieldActions.familyFieldPeriodAction RepresentationTheory.Theta.Geometric.Family.PELCoordinates.familyPELCoordinates
  RepresentationTheory.Theta.Geometric.Intrinsic.CompatibleTransport.NativeCompatibleTransport.normalizedHodgeLine RepresentationTheory.Theta.Geometric.Family.EmbeddingInclusion.familyEmbeddingInclusion Family.MarkingCoordinates.markingComplexBasis

variable {E : Type} [Field E] [NumberField E] {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    {A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left}
    {ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian}
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport A ρ F)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

def Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.embeddingCoefficients (τ : E →ₐ[ℚ] ℂ) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) : Geometry.ComplexBall.PrescribedSignsB.Vec →L[ℂ] (Fin F.rank → ℂ) :=
  ((Family.MarkingCoordinates.markingComplexBasis H.centralMarking).equivFun.toLinearMap.comp
    ((RepresentationTheory.Theta.Geometric.Family.EmbeddingInclusion.familyEmbeddingInclusion A ρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree τ).comp
      e₀.toLinearMap)).toContinuousLinearMap

def Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.embeddingMatrix (τ : E →ₐ[ℚ] ℂ) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C) :
    Geometry.ComplexBall.PrescribedSignsB.Vec →L[ℂ] (Fin H.dimension → ℂ) :=
  (H.matrix z).comp (H.embeddingCoefficients s hs hg hdegree τ e₀)

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.embeddingMatrix_apply (τ : E →ₐ[ℚ] ℂ) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    H.embeddingMatrix s hs hg hdegree τ e₀ z v =
      H.matrix z ((Family.MarkingCoordinates.markingComplexBasis H.centralMarking).equivFun
        (RepresentationTheory.Theta.Geometric.Family.EmbeddingInclusion.familyEmbeddingInclusion A ρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree τ (e₀ v))) := by
  unfold Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.embeddingMatrix Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.embeddingCoefficients
  change H.matrix z (((Family.MarkingCoordinates.markingComplexBasis H.centralMarking).equivFun.toLinearMap.comp
    ((RepresentationTheory.Theta.Geometric.Family.EmbeddingInclusion.familyEmbeddingInclusion A ρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree τ).comp
      e₀.toLinearMap)) v) = _
  rfl

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.embeddingMatrix_holomorphic (τ : E →ₐ[ℚ] ℂ) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) :
    DifferentiableOn ℂ (H.embeddingMatrix s hs hg hdegree τ e₀) H.compatible.neighborhood := by
  change DifferentiableOn ℂ (fun z => (H.matrix z).comp (H.embeddingCoefficients s hs hg hdegree τ e₀))
    H.compatible.neighborhood
  exact H.holomorphic.clm_comp (differentiableOn_const (H.embeddingCoefficients s hs hg hdegree τ e₀))

attribute [local irreducible] Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.embeddingMatrix Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.embeddingCoefficients

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.embeddingMatrix_kernel (τ : E →ₐ[ℚ] ℂ) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z : H.compatible.neighborhood) :
    (H.embeddingMatrix s hs hg hdegree τ e₀ z).ker =
      H.compatible.normalizedHodgeLine A ρ s hs hg hdegree τ e₀ z := by
  apply Submodule.ext
  intro v
  change H.embeddingMatrix s hs hg hdegree τ e₀ z v = 0 ↔ _
  rw [H.embeddingMatrix_apply, H.matrix_kernel_iff]
  change Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety
    ((F.nativeRationalTransport z (H.compatible.subset_frame z.property) (H.compatible.subset_chart z.property)
      (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)))
      (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z))).baseChange ℂ
      (RepresentationTheory.Theta.Geometric.Family.EmbeddingInclusion.familyEmbeddingInclusion A ρ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree τ (e₀ v))) = 0 ↔ _
  rw [H.compatible.embeddingInclusion_transport, RepresentationTheory.Theta.Geometric.Family.EmbeddingInclusion.familyEmbeddingInclusion_kernel]
  unfold RepresentationTheory.Theta.Geometric.Intrinsic.CompatibleTransport.NativeCompatibleTransport.normalizedHodgeLine Normalized.HodgeLine.NativeHermitianMarking.nativeNormalizedHodgeLine
  rw [Submodule.mem_map_equiv]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
