import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.ChernTransport
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.RationalTransport

/-! # Chern Form -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Full native rational period transport preserves the actual Chern
form of every line bundle restricted from the total abelian family. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

/-- The Chern form of a line bundle is preserved by the rational period transport from the
center of a native family chart to a point of a common transport neighborhood. -/
def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.PreservesNativeChernForm
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S,
      ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left))
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle
      (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G).left)
    {U : Set (Intrinsic.FamilyFrames.FamilyChartBase C)}
    (hU : U ⊆ F.neighborhood) (hN : U ⊆ C.charts.charts.neighborhood) (z : U) : Prop :=
  let P := fun y => present (Intrinsic.FamilyFrames.familyChartParameter C y)
  ∀ (v w : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods
      (P (Intrinsic.FamilyFrames.familyChartCenter C)).variety),
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm
        (P (Intrinsic.FamilyFrames.familyChartCenter C)).variety
        (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberLine
          (C := C) (Intrinsic.FamilyFrames.familyChartCenter C)
          (P (Intrinsic.FamilyFrames.familyChartCenter C)) L) v w =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm (P z).variety
        (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberLine
          (C := C) z (P z) L)
        (F.nativeRationalTransport z (hU z.property) (hN z.property)
          (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z) v)
        (F.nativeRationalTransport z (hU z.property) (hN z.property)
          (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z) w)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.exists_constant_native_chern_form
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left))
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G).left) :
    ∃ U : Set (Intrinsic.FamilyFrames.FamilyChartBase C), IsOpen U ∧ Intrinsic.FamilyFrames.familyChartCenter C ∈ U ∧
      ∃ (hU : U ⊆ F.neighborhood) (hN : U ⊆ C.charts.charts.neighborhood),
        ∀ z : U, F.PreservesNativeChernForm present L hU hN z := by
  let P := fun z => present (Intrinsic.FamilyFrames.familyChartParameter C z)
  obtain ⟨U, hUopen, hxU, hU, hN, hchern⟩ := F.exists_native_chern_transport present L
  refine ⟨U, hUopen, hxU, hU, hN, ?_⟩
  intro z
  dsimp only [Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.PreservesNativeChernForm]
  intro v w
  exact F.nativeChernForm_transport z (hU z.property) (hN z.property)
    (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z)
    (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberLine (C := C) (Intrinsic.FamilyFrames.familyChartCenter C) (P (Intrinsic.FamilyFrames.familyChartCenter C)) L)
    (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberLine (C := C) z (P z) L) (hchern z) v w

end

end OAI.RepresentationTheory.Theta.Geometric
