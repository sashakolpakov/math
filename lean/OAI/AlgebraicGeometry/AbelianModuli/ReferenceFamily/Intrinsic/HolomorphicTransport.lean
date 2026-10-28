import OAI.RepresentationTheory.Theta.Geometric.CompatibleTransportRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MarkedTransport

/-! # Holomorphic Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport

noncomputable section

/-! Constructed holomorphic native period matrices together with the
same original polarization, full field action, and full-level transport. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

attribute [local irreducible] RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm RepresentationTheory.Theta.Geometric.Family.FieldActions.familyFieldPeriodAction

local instance nativeHolomorphicTransport_varietyIntegral (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property

variable {E : Type} [Field E] [NumberField E] {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    (F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

structure NativeFamilyHolomorphicTransport where
  compatible : RepresentationTheory.Theta.Geometric.Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F
  dimension : ℕ
  coordinates : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartTangent C ≃L[ℂ] (Fin dimension → ℂ)
  tangentCoordinates : ∀ z : compatible.neighborhood,
    RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartTangent C ≃L[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety
  marking : ∀ z : compatible.neighborhood,
    ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Fin F.rank) (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety
  matrix : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C → (Fin F.rank → ℂ) →L[ℂ] (Fin dimension → ℂ)
  marking_eq : ∀ (z : compatible.neighborhood) i,
    (marking z i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety) =
      tangentCoordinates z (F.periods z (Pi.single i 1))
  matrix_eq : ∀ z : compatible.neighborhood, matrix z =
    (((tangentCoordinates z).symm.trans coordinates).toLinearEquiv.toLinearMap.comp
      (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (marking z))).toContinuousLinearMap
  holomorphic : DifferentiableOn ℂ matrix compatible.neighborhood
  marking_transport : ∀ (z : compatible.neighborhood) i,
    F.nativeRealTransport z (compatible.subset_chart z.property)
      (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)))
      (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z))
      (marking ⟨RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C, compatible.center⟩ i :
        HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C))).variety) =
      (marking z i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety)

theorem exists_nativeFamilyHolomorphicTransport (hN : 0 < N) : Nonempty (NativeFamilyHolomorphicTransport A ρ F) := by
  obtain ⟨D⟩ := RepresentationTheory.Theta.Geometric.Intrinsic.CompatibleTransport.exists_nativeCompatibleTransport A ρ F hN
  obtain ⟨U, hU, hx, _hUF, _hUN, d, e, T, marking, matrix, hb, hm, hhol, ht⟩ :=
    MarkedTransport.nativeFamilyFrame_holomorphic_marked_transport F (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A)
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

theorem exists_native_family_holomorphic_transport
    {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral T.left] [Smooth T.hom]
    (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints T) (hN : 0 < N) :
    ∃ (D : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts B.abelian y) (V : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame D),
      Nonempty (NativeFamilyHolomorphicTransport B σ V) := by
  obtain ⟨D⟩ := PELModuli.CMPoints.IntrinsicFamilyCharts.exists_native_family_charts B.abelian y
  obtain ⟨V⟩ := RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.exists_nativeFamilyPeriodFrame D (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation B)
  exact ⟨D, V, exists_nativeFamilyHolomorphicTransport B σ V hN⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTransport
