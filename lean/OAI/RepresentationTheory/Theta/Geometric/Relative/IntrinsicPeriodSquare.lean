import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.BetweenRationalValues
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.BetweenCenter
import OAI.RepresentationTheory.Theta.Geometric.EquivalenceSquares

/-! # Intrinsic Period Square -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Geometric.Relative.IntrinsicPeriodSquare

/-! Exact rational and full-level comparisons for the actual native
transport between two fibers through their common center. -/

end RepresentationTheory.Theta.Geometric.Relative.IntrinsicPeriodSquare

namespace RepresentationTheory.Theta.Geometric

/-! The actual fiber homeomorphism between any two points has exactly
the real period lift given by their common native frame. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped Classical

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation Family.FieldActions.familyFieldPeriodAction Family.PELCoordinates.familyPELCoordinates

local instance Relative.IntrinsicPeriodSquare.relativeNativePeriodSquare_integral (B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property

variable {E : Type} [Field E] [NumberField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.fiberBetween_period (z w : D.neighborhood)
    (v : AlgebraicAction.AbelianModel (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety) :
    D.fiberBetween A ρ z w
      (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety
        (QuotientAddGroup.mk v)) =
      AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)).variety
        (QuotientAddGroup.mk (D.realBetween A ρ z w v)) := by
  let P₀ := PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))
  let Pz := PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)
  let Pw := PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)
  exact EquivalenceSquares.equivalence_square_between
    (fun a : AlgebraicAction.AbelianModel P₀.variety => AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input P₀.variety (QuotientAddGroup.mk a))
    (fun a : AlgebraicAction.AbelianModel Pz.variety => AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input Pz.variety (QuotientAddGroup.mk a))
    (fun a : AlgebraicAction.AbelianModel Pw.variety => AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input Pw.variety (QuotientAddGroup.mk a))
    (F.nativeFiberTransport z (D.subset_frame z.property) (D.subset_chart z.property) P₀ Pz).toEquiv
    (F.nativeFiberTransport w (D.subset_frame w.property) (D.subset_chart w.property) P₀ Pw).toEquiv
    (F.nativeRealTransport z (D.subset_chart z.property) P₀ Pz).toEquiv
    (F.nativeRealTransport w (D.subset_chart w.property) P₀ Pw).toEquiv
    (F.nativeFiberTransport_period z (D.subset_frame z.property) (D.subset_chart z.property) P₀ Pz)
    (F.nativeFiberTransport_period w (D.subset_frame w.property) (D.subset_chart w.property) P₀ Pw) v

end RepresentationTheory.Theta.Geometric

end

end OAI
