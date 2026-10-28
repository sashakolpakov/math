import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.RealTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses

/-! # Chern Maps -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Named actual maps and line restrictions used in the fiber Chern comparison. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.nativePointTransport (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) :
    TopCat.of (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P₀.variety.toOver) ⟶ TopCat.of (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.variety.toOver) :=
  TopCat.ofHom ⟨F.nativeFiberTransport z hz hzN P₀ P, (F.nativeFiberTransport z hz hzN P₀ P).continuous⟩

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberLine (z : Intrinsic.FamilyFrames.FamilyChartBase C)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z))
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G).left) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle P.variety.toOver.left :=
  L.pullback (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberInclusion (C := C) z P).left

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberChern (z : Intrinsic.FamilyFrames.FamilyChartBase C)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z))
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G).left) : P.variety.variety.rationalCohomology 2 :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass P.variety.variety.presentation (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberLine (C := C) z P L)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.nativePointTransport_square (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) :
    TopCat.ofHom (F.presentedTorusMap (Intrinsic.FamilyFrames.familyChartCenter C) F.center P₀) ≫
      F.nativePointTransport z hz hzN P₀ P = TopCat.ofHom (F.presentedTorusMap z hz P) := by
  apply TopCat.ext
  intro v
  change F.nativeFiberTransport z hz hzN P₀ P
    (F.presentedTorusMap (Intrinsic.FamilyFrames.familyChartCenter C) F.center P₀ v) = F.presentedTorusMap z hz P v
  rw [← F.presentedTorusHomeomorph_apply (Intrinsic.FamilyFrames.familyChartCenter C) F.center (Family.ChartOpenImage.familyChartCenter_mem C) P₀]
  change F.presentedTorusHomeomorph z hz hzN P
    ((F.presentedTorusHomeomorph (Intrinsic.FamilyFrames.familyChartCenter C) F.center (Family.ChartOpenImage.familyChartCenter_mem C) P₀).symm
      ((F.presentedTorusHomeomorph (Intrinsic.FamilyFrames.familyChartCenter C) F.center (Family.ChartOpenImage.familyChartCenter_mem C) P₀) v)) = _
  rw [Homeomorph.symm_apply_apply, F.presentedTorusHomeomorph_apply]

end

end OAI.RepresentationTheory.Theta.Geometric
