import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames

/-! # Chart Open Image -/

namespace OAI.RepresentationTheory.Theta.Geometric.Family.ChartOpenImage

noncomputable section

section

/-! The constructed period-chart parameters retain the original central
scheme point and are injective on their actual base neighborhood. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} (C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x)

theorem familyChartCenter_mem : Intrinsic.FamilyFrames.familyChartCenter C ∈ C.charts.charts.neighborhood := by
  simpa only [Intrinsic.FamilyFrames.familyChartCenter, AlgHom.comp_assoc, C.charts.retraction, AlgHom.comp_id]
    using C.charts.charts.center

theorem familyChartParameter_center : Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C) = x := by
  have hx : C.point ∈ C.charts.charts.charts.base.source := by
    simpa only [AlgHom.comp_assoc, C.charts.retraction, AlgHom.comp_id]
      using C.charts.charts.charts.basePoint
  change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap C.algebra C.openMap
    (C.charts.charts.charts.base.symm (C.charts.charts.charts.base C.point)) = x
  rw [C.charts.charts.charts.base.left_inv hx]
  exact C.center

theorem familyChartParameter_injective :
    Set.InjOn (Intrinsic.FamilyFrames.familyChartParameter C) C.charts.charts.neighborhood := by
  intro z hz w hw he
  have h := (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap C.algebra C.openMap).injective he
  exact C.charts.charts.charts.base.symm.injOn
    (C.charts.charts.withinBase hz) (C.charts.charts.withinBase hw) h

theorem familyChartParameter_continuous :
    ContinuousOn (Intrinsic.FamilyFrames.familyChartParameter C) C.charts.charts.neighborhood :=
  (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap C.algebra C.openMap).continuous.comp_continuousOn
    (C.charts.charts.charts.base.symm.continuousOn.mono C.charts.charts.withinBase)

end

/-! The actual chart parameter map sends open subsets of its native
coordinate neighborhood to open subsets of the original scheme points. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

theorem familyChartParameter_open_image {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ}
    {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left} {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    (C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x) (U : Set (Intrinsic.FamilyFrames.FamilyChartBase C)) (hU : IsOpen U)
    (hsub : U ⊆ C.charts.charts.neighborhood) : IsOpen (Intrinsic.FamilyFrames.familyChartParameter C '' U) := by
  have hi := C.charts.charts.charts.base.isOpen_image_symm_of_subset_target hU
    (hsub.trans C.charts.charts.withinBase)
  have h := (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap C.algebra C.openMap).isOpenMap _ hi
  simpa only [Set.image_image, Intrinsic.FamilyFrames.familyChartParameter, Function.comp_def] using h

end

end OAI.RepresentationTheory.Theta.Geometric.Family.ChartOpenImage
