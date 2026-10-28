import OAI.RepresentationTheory.Theta.Geometric.Family.MarkedPeriodTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingMatrixTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingChernMatrix

/-! # Complex Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual common transport acts in every complex embedding block
by the embedded matrix of its rank-three field-coordinate change. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingMatrixTransport OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingChernMatrix.IntrinsicHermitianMarking

variable {E : Type} [Field E] [NumberField E] {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

def Family.ComplexCoordinates.familyComplexCoordinates (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (s : ℕ) (hs : 0 < s)
    (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s) :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A y).variety) ≃ₗ[ℂ]
      ((E →ₐ[ℚ] ℂ) → Fin 3 → ℂ) := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ y
  let := Family.PELCoordinates.familyPeriodScalarTower A ρ y
  exact AlgebraicGeometry.AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E (Family.PELCoordinates.familyPELCoordinates A ρ y s hs hg hdegree)

theorem Family.ComplexCoordinates.familyComplexCoordinates_original (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (s : ℕ) (hs : 0 < s)
    (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s) :
    Family.ComplexCoordinates.familyComplexCoordinates A ρ y s hs hg hdegree =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates (A.pullback y.left) (ρ.pullback y.left) s hs hg hdegree := rfl

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation Family.FieldActions.familyFieldPeriodAction Family.PELCoordinates.familyPELCoordinates

variable {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.complexCoordinates_transport (z : D.neighborhood)
    (v : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))).variety))
    (τ : E →ₐ[ℚ] ℂ) :
    Family.ComplexCoordinates.familyComplexCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree
      ((F.nativeRationalTransport z (D.subset_frame z.property) (D.subset_chart z.property)
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z))).baseChange ℂ v) τ =
      ((LinearMap.toMatrix' (D.coordinateTransport A ρ s hs hg hdegree z).toLinearMap).map τ).mulVec
        (Family.ComplexCoordinates.familyComplexCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree v τ) := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))
  let := Family.PELCoordinates.familyPeriodScalarTower A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C z)
  let := Family.PELCoordinates.familyPeriodScalarTower A ρ (Intrinsic.FamilyFrames.familyChartParameter C z)
  exact AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingMatrixTransport.rankThreeComplexCoordinates_map
    (Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree)
    (Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree)
    (F.nativeRationalTransport z (D.subset_frame z.property) (D.subset_chart z.property)
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)))
    (D.coordinateTransport A ρ s hs hg hdegree z).toLinearMap
    (fun w => (D.coordinateTransport_apply A ρ s hs hg hdegree z w).symm) v τ

end

end OAI.RepresentationTheory.Theta.Geometric
