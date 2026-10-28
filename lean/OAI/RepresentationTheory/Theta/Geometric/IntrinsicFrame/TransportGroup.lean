import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.RealTransport

/-! # Transport Group -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The real period transport between the original native fibers is
an actual continuous group isomorphism. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedTorusHomeomorph_mul (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) (v w : F.CentralTorus) :
    F.presentedTorusHomeomorph z hz hzN P (v + w) =
      F.presentedTorusHomeomorph z hz hzN P v * F.presentedTorusHomeomorph z hz hzN P w := by
  rw [F.presentedTorusHomeomorph_apply, F.presentedTorusHomeomorph_apply,
    F.presentedTorusHomeomorph_apply, F.presentedTorusMap_add]

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedTorusHomeomorph_symm_mul (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z))
    (v w : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.variety.toOver) :
    (F.presentedTorusHomeomorph z hz hzN P).symm (v * w) =
      (F.presentedTorusHomeomorph z hz hzN P).symm v + (F.presentedTorusHomeomorph z hz hzN P).symm w := by
  apply (F.presentedTorusHomeomorph z hz hzN P).injective
  rw [F.presentedTorusHomeomorph_mul, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.nativeFiberTransport_mul (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z))
    (v w : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P₀.variety.toOver) :
    F.nativeFiberTransport z hz hzN P₀ P (v * w) =
      F.nativeFiberTransport z hz hzN P₀ P v * F.nativeFiberTransport z hz hzN P₀ P w := by
  change F.presentedTorusHomeomorph z hz hzN P
    ((F.presentedTorusHomeomorph (Intrinsic.FamilyFrames.familyChartCenter C) F.center (Family.ChartOpenImage.familyChartCenter_mem C) P₀).symm (v * w)) = _
  rw [F.presentedTorusHomeomorph_symm_mul, F.presentedTorusHomeomorph_mul]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric
