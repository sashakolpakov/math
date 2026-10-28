import OAI.RepresentationTheory.Theta.Geometric.Finite.EndomorphismTransport
import OAI.RepresentationTheory.Theta.Geometric.Family.FieldActions
import OAI.RepresentationTheory.Theta.Geometric.IntegralBasisIntertwining

/-! # Field Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual full number-field action is retained on one constructed
neighborhood by using its finite integral basis and the same rational transport. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation Family.FieldActions.familyFieldPeriodAction Family.FieldActions.familyIntegralPeriodAction

variable {E : Type} [Field E] [NumberField E] {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.exists_field_action_transport (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C) :
    let P := fun z => PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)
    ∃ U : Set (Intrinsic.FamilyFrames.FamilyChartBase C), IsOpen U ∧ Intrinsic.FamilyFrames.familyChartCenter C ∈ U ∧
      ∃ (hU : U ⊆ F.neighborhood) (hN : U ⊆ C.charts.charts.neighborhood),
        ∀ (z : U) (a : E) (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (P (Intrinsic.FamilyFrames.familyChartCenter C)).variety),
          Family.FieldActions.familyFieldPeriodAction A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) a
            (F.nativeRationalTransport z (hU z.property) (hN z.property) (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z) v) =
          F.nativeRationalTransport z (hU z.property) (hN z.property) (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z)
            (Family.FieldActions.familyFieldPeriodAction A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) a v) := by
  let P := fun z => PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)
  let k := fun i : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers E) =>
    ρ.map (NumberField.RingOfIntegers.basis E i)
  let (i : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers E)) : IsMonHom (k i) :=
    ρ.preservesGroup _
  obtain ⟨U, hUopen, hxU, hU, hN, hcomm⟩ :=
    F.exists_finite_rational_endomorphism_transport (PolarizedCanonicalForm.polarizedFamilyPresentation A) k
  refine ⟨U, hUopen, hxU, hU, hN, ?_⟩
  intro z a v
  apply IntegralBasisIntertwining.integralBasis_fieldAction_intertwining
    (Family.FieldActions.familyFieldPeriodAction A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (Family.FieldActions.familyFieldPeriodAction A ρ (Intrinsic.FamilyFrames.familyChartParameter C z))
    (F.nativeRationalTransport z (hU z.property) (hN z.property) (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z))
    (fun i w => ?_) a v
  rw [NumberField.integralBasis_apply, Family.FieldActions.familyFieldPeriodAction_integer, Family.FieldActions.familyFieldPeriodAction_integer,
    Family.FieldActions.familyIntegralPeriodAction_frame A ρ C z,
    Family.FieldActions.familyIntegralPeriodAction_frame A ρ C (Intrinsic.FamilyFrames.familyChartCenter C)]
  exact hcomm z i w

end

end OAI.RepresentationTheory.Theta.Geometric
