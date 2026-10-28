import OAI.RepresentationTheory.Theta.Geometric.Relative.MarkedTransport
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FrameRationalEquiv

/-! # Integral Polarization -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual comparison of two fibers preserves the full integral
lattice and the original rational polarization, with their exact forms. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation PolarizedCanonicalForm.familyPolarizationForm Family.FieldActions.familyFieldPeriodAction
  Family.PELCoordinates.familyPELCoordinates AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods

variable {E : Type} [Field E] [NumberField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.rationalBetween_integral (z w : D.neighborhood)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety) :
    D.rationalBetween A ρ z w v ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)).variety ↔
      v ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety := by
  obtain ⟨v₀, rfl⟩ := (F.nativeRationalEquiv z (D.subset_frame z.property) (D.subset_chart z.property)
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z))).surjective v
  have he := congrArg (fun t => t ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)).variety)
    (D.rationalBetween_apply_center A ρ z w v₀)
  exact he.to_iff.trans ((F.nativeRationalEquiv_integral w (D.subset_frame w.property) (D.subset_chart w.property)
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)) v₀).trans
      (F.nativeRationalEquiv_integral z (D.subset_frame z.property) (D.subset_chart z.property)
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)) v₀).symm)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.rationalBetween_polarization (z w : D.neighborhood)
    (v u : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety) :
    PolarizedCanonicalForm.familyPolarizationForm A (Intrinsic.FamilyFrames.familyChartParameter C w)
      (D.rationalBetween A ρ z w v) (D.rationalBetween A ρ z w u) =
      PolarizedCanonicalForm.familyPolarizationForm A (Intrinsic.FamilyFrames.familyChartParameter C z) v u := by
  let e := F.nativeRationalEquiv z (D.subset_frame z.property) (D.subset_chart z.property)
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z))
  obtain ⟨v₀, rfl⟩ := e.surjective v
  obtain ⟨u₀, rfl⟩ := e.surjective u
  have he := congrArg₂ (fun v u => PolarizedCanonicalForm.familyPolarizationForm A (Intrinsic.FamilyFrames.familyChartParameter C w) v u)
    (D.rationalBetween_apply_center A ρ z w v₀) (D.rationalBetween_apply_center A ρ z w u₀)
  exact he.trans ((D.polarization w v₀ u₀).symm.trans (D.polarization z v₀ u₀))

end

end OAI.RepresentationTheory.Theta.Geometric
