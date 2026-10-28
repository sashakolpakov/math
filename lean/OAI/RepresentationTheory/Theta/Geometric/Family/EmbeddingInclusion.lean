import OAI.RepresentationTheory.Theta.Geometric.Family.ComplexCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup

/-! # Embedding Inclusion -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Geometric.Family.EmbeddingInclusion

/-! Literal inclusion of one embedding block in the actual rational
complexification, with its exact native Hodge-kernel criterion. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking

variable {E : Type} [Field E] [NumberField E] {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

def familyEmbeddingInclusion (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (s : ℕ) (hs : 0 < s)
    (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s) (τ : E →ₐ[ℚ] ℂ) :
    (Fin 3 → ℂ) →ₗ[ℂ] AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A y).variety) :=
  (ComplexCoordinates.familyComplexCoordinates A ρ y s hs hg hdegree).symm.toLinearMap.comp
    (LinearMap.single ℂ (fun _ : E →ₐ[ℚ] ℂ => Fin 3 → ℂ) τ)

theorem familyEmbeddingInclusion_coordinates (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (s : ℕ) (hs : 0 < s)
    (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s) (τ : E →ₐ[ℚ] ℂ) (v : Fin 3 → ℂ) :
    ComplexCoordinates.familyComplexCoordinates A ρ y s hs hg hdegree
      (familyEmbeddingInclusion A ρ y s hs hg hdegree τ v) = Pi.single τ v :=
  (ComplexCoordinates.familyComplexCoordinates A ρ y s hs hg hdegree).apply_symm_apply _

theorem familyEmbeddingInclusion_native (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (s : ℕ) (hs : 0 < s)
    (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s) (τ : E →ₐ[ℚ] ℂ) (v : Fin 3 → ℂ) :
    familyEmbeddingInclusion A ρ y s hs hg hdegree τ v =
      ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeEmbeddingCoordinateEquiv (A.pullback y.left) (ρ.pullback y.left) s hs hg hdegree τ).symm v).val := rfl

theorem familyEmbeddingInclusion_kernel (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (s : ℕ) (hs : 0 < s)
    (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s) (τ : E →ₐ[ℚ] ℂ) (v : Fin 3 → ℂ) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (PolarizedCanonicalForm.polarizedFamilyPresentation A y).variety
      (familyEmbeddingInclusion A ρ y s hs hg hdegree τ v) = 0 ↔
      v ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart (A.pullback y.left) (ρ.pullback y.left) s hs hg hdegree τ := by
  rw [familyEmbeddingInclusion_native]
  unfold AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart
  rw [Submodule.mem_map_equiv]
  rfl

end RepresentationTheory.Theta.Geometric.Family.EmbeddingInclusion

namespace RepresentationTheory.Theta.Geometric

/-! The actual rational transport carries each fixed embedding inclusion
to the corresponding moving inclusion by its embedded field matrix. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation Family.FieldActions.familyFieldPeriodAction Family.PELCoordinates.familyPELCoordinates

variable {E : Type} [Field E] [NumberField E] {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.embeddingInclusion_transport (z : D.neighborhood) (τ : E →ₐ[ℚ] ℂ) (v : Fin 3 → ℂ) :
    (F.nativeRationalTransport z (D.subset_frame z.property) (D.subset_chart z.property)
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z))).baseChange ℂ
        (Family.EmbeddingInclusion.familyEmbeddingInclusion A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree τ v) =
      Family.EmbeddingInclusion.familyEmbeddingInclusion A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree τ
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (D.coordinateTransport A ρ s hs hg hdegree z) τ v) := by
  apply (Family.ComplexCoordinates.familyComplexCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree).injective
  rw [Family.EmbeddingInclusion.familyEmbeddingInclusion_coordinates]
  funext κ
  rw [D.complexCoordinates_transport, Family.EmbeddingInclusion.familyEmbeddingInclusion_coordinates]
  by_cases hκ : κ = τ
  · subst κ
    simp only [Pi.single_eq_same, AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso_apply]
  · simp only [Pi.single_eq_of_ne hκ, Matrix.mulVec_zero]

end RepresentationTheory.Theta.Geometric

end

end OAI
