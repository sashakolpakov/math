import OAI.RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.ChernMaps

/-! # Frame Diagonal Form -/

namespace OAI.RepresentationTheory.Theta.Geometric.FrameDiagonalForm

noncomputable section

/-! The canonical diagonal form comparison in the literal family-chart
restriction used by the fixed-torus construction. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)

def familyPolarizationDiagonalLine : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S A.abelian).left :=
  Relative.DiagonalLine.relativeDiagonalLine A.dual A.polarization.isogeny.hom

variable {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} (C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x)

theorem frameDiagonalForm (z : Intrinsic.FamilyFrames.FamilyChartBase C)
    (v w : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety
      (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberLine (C := C) z
        (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)) (familyPolarizationDiagonalLine A)) v w =
      2 * PolarizedCanonicalForm.familyPolarizationForm A (Intrinsic.FamilyFrames.familyChartParameter C z) v w :=
  PolarizedCanonicalForm.familyDiagonalForm A (Intrinsic.FamilyFrames.familyChartParameter C z) v w

end

end OAI.RepresentationTheory.Theta.Geometric.FrameDiagonalForm
