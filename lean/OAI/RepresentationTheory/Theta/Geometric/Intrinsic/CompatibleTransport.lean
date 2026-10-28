import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.FieldTransport
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.Polarization
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.LevelTransport

/-! # Compatible Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CompatibleTransport

noncomputable section

/-! One constructed neighborhood retains the original polarization,
full number-field action, and full level in the same native period frame. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation PolarizedCanonicalForm.familyPolarizationForm Family.FieldActions.familyFieldPeriodAction

variable {E : Type} [Field E] [NumberField E] {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    (F : FamilyFrames.NativeFamilyPeriodFrame C)

structure NativeCompatibleTransport where
  neighborhood : Set (FamilyFrames.FamilyChartBase C)
  isOpen : IsOpen neighborhood
  center : FamilyFrames.familyChartCenter C ∈ neighborhood
  subset_frame : neighborhood ⊆ F.neighborhood
  subset_chart : neighborhood ⊆ C.charts.charts.neighborhood
  polarization : ∀ (z : neighborhood)
    (v w : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C))).variety),
    PolarizedCanonicalForm.familyPolarizationForm A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)) v w =
      PolarizedCanonicalForm.familyPolarizationForm A (FamilyFrames.familyChartParameter C z)
        (F.nativeRationalTransport z (subset_frame z.property) (subset_chart z.property)
          (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)))
          (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z)) v)
        (F.nativeRationalTransport z (subset_frame z.property) (subset_chart z.property)
          (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)))
          (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z)) w)
  field : ∀ (z : neighborhood) (a : E)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C))).variety),
    Family.FieldActions.familyFieldPeriodAction A ρ (FamilyFrames.familyChartParameter C z) a
      (F.nativeRationalTransport z (subset_frame z.property) (subset_chart z.property)
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)))
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z)) v) =
    F.nativeRationalTransport z (subset_frame z.property) (subset_chart z.property)
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)))
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z))
      (Family.FieldActions.familyFieldPeriodAction A ρ (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)) a v)
  level : ∀ (z : neighborhood) (a : Multiplicative (Fin (2 * g) → ZMod N)),
    F.nativeFiberTransport z (subset_frame z.property) (subset_chart z.property)
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)))
      (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z))
      (LevelTransport.presentedFullLevelPoint A.level (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C))
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C))) a) =
      LevelTransport.presentedFullLevelPoint A.level (FamilyFrames.familyChartParameter C z)
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (FamilyFrames.familyChartParameter C z)) a

theorem exists_nativeCompatibleTransport (hN : 0 < N) : Nonempty (NativeCompatibleTransport A ρ F) := by
  obtain ⟨U₁, hU₁, hx₁, hF₁, hC₁, hp⟩ := F.exists_constant_polarization_form A
  obtain ⟨U₂, hU₂, hx₂, hF₂, hC₂, hf⟩ := F.exists_field_action_transport A ρ
  obtain ⟨U₃, hU₃, hx₃, hF₃, hC₃, hl⟩ :=
    F.exists_native_full_level_transport (PolarizedCanonicalForm.polarizedFamilyPresentation A) N hN A.level
  let U := (U₁ ∩ U₂) ∩ U₃
  exact ⟨{
    neighborhood := U
    isOpen := (hU₁.inter hU₂).inter hU₃
    center := ⟨⟨hx₁, hx₂⟩, hx₃⟩
    subset_frame := fun _ hz => hF₁ hz.1.1
    subset_chart := fun _ hz => hC₁ hz.1.1
    polarization := fun z v w => hp ⟨z.val, z.property.1.1⟩ v w
    field := fun z a v => hf ⟨z.val, z.property.1.2⟩ a v
    level := fun z a => hl ⟨z.val, z.property.2⟩ a }⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CompatibleTransport
