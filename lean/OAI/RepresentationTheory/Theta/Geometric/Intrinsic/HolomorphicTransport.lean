import OAI.RepresentationTheory.Theta.Geometric.CompatibleTransportRestriction
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.MarkedTransport

/-! # Holomorphic Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.HolomorphicTransport

noncomputable section

/-! Constructed holomorphic native period matrices together with the
same original polarization, full field action, and full-level transport. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation PolarizedCanonicalForm.familyPolarizationForm Family.FieldActions.familyFieldPeriodAction

local instance nativeHolomorphicTransport_varietyIntegral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property

variable {E : Type} [Field E] [NumberField E] {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    (F : FamilyFrames.NativeFamilyPeriodFrame C)

structure NativeHolomorphicTransport where
  compatible : CompatibleTransport.NativeCompatibleTransport A ρ F
  dimension : ℕ
  coordinates : FamilyFrames.FamilyChartTangent C ≃L[ℂ] (Fin dimension → ℂ)
  tangentCoordinates : ∀ z : compatible.neighborhood,
    FamilyFrames.FamilyChartTangent C ≃L[ℂ] AlgebraicAction.AbelianModel (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z)).variety
  marking : ∀ z : compatible.neighborhood,
    ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Fin F.rank) (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z)).variety
  matrix : FamilyFrames.FamilyChartBase C → (Fin F.rank → ℂ) →L[ℂ] (Fin dimension → ℂ)
  marking_eq : ∀ (z : compatible.neighborhood) i,
    (marking z i : AlgebraicAction.AbelianModel (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z)).variety) =
      tangentCoordinates z (F.periods z (Pi.single i 1))
  matrix_eq : ∀ z : compatible.neighborhood, matrix z =
    (((tangentCoordinates z).symm.trans coordinates).toLinearEquiv.toLinearMap.comp
      (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (marking z))).toContinuousLinearMap
  holomorphic : DifferentiableOn ℂ matrix compatible.neighborhood
  marking_transport : ∀ (z : compatible.neighborhood) i,
    F.nativeRealTransport z (compatible.subset_chart z.property)
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)))
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z))
      (marking ⟨FamilyFrames.familyChartCenter C, compatible.center⟩ i :
        AlgebraicAction.AbelianModel (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C))).variety) =
      (marking z i : AlgebraicAction.AbelianModel (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z)).variety)

theorem exists_nativeHolomorphicTransport (hN : 0 < N) : Nonempty (NativeHolomorphicTransport A ρ F) := by
  obtain ⟨D⟩ := CompatibleTransport.exists_nativeCompatibleTransport A ρ F hN
  obtain ⟨U, hU, hx, _hUF, _hUN, d, e, T, marking, matrix, hb, hm, hhol, ht⟩ :=
    F.exists_holomorphic_marked_transport (PolarizedCanonicalForm.polarizedFamilyPresentation A)
  let V := D.neighborhood ∩ U
  let D' := D.restrict V (D.isOpen.inter hU) ⟨D.center, hx⟩ Set.inter_subset_left
  let intoU (z : D'.neighborhood) : U := ⟨z.val, z.property.2⟩
  exact ⟨{
    compatible := D'
    dimension := d
    coordinates := e
    tangentCoordinates := fun z => T (intoU z)
    marking := fun z => marking (intoU z)
    matrix := matrix
    marking_eq := fun z i => hb (intoU z) i
    matrix_eq := fun z => hm (intoU z)
    holomorphic := hhol.mono Set.inter_subset_right
    marking_transport := fun z i => ht (intoU z) i }⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.HolomorphicTransport
