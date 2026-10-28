import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.ChernMaps
import OAI.RepresentationTheory.Theta.Geometric.CohomologyHomeomorphCancellation

/-! # Chern Cancel -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Cancel the actual central-torus homeomorphism in the native Chern comparison. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.cancel_central_chern_comparison (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z))
    (c₀ : P₀.variety.variety.rationalCohomology 2) (c : P.variety.variety.rationalCohomology 2)
    (h : AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (F.presentedTorusMap (Intrinsic.FamilyFrames.familyChartCenter C) F.center P₀)) 2 c₀ =
        AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (TopCat.ofHom (F.presentedTorusMap z hz P)) 2 c) :
    c₀ = AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (F.nativePointTransport z hz hzN P₀ P) 2 c := by
  let e₀ := F.presentedTorusHomeomorph (Intrinsic.FamilyFrames.familyChartCenter C) F.center (Family.ChartOpenImage.familyChartCenter_mem C) P₀
  have he₀ : TopCat.ofHom ⟨e₀, e₀.continuous⟩ =
      TopCat.ofHom (F.presentedTorusMap (Intrinsic.FamilyFrames.familyChartCenter C) F.center P₀) := by
    apply TopCat.ext
    intro v
    exact F.presentedTorusHomeomorph_apply _ _ _ _ v
  apply CohomologyHomeomorphCancellation.cohomologyPullback_homeomorph_injective (X := TopCat.of F.CentralTorus)
    (Y := TopCat.of (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P₀.variety.toOver)) (ModuleCat.of ℚ ℚ) e₀ 2
  rw [he₀]
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (F.presentedTorusMap (Intrinsic.FamilyFrames.familyChartCenter C) F.center P₀))
      (F.nativePointTransport z hz hzN P₀ P) 2) c
  rw [F.nativePointTransport_square z hz hzN P₀ P] at hc
  exact h.trans hc

end

end OAI.RepresentationTheory.Theta.Geometric
