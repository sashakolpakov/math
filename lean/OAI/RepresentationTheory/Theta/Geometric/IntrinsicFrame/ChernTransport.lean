import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.Chern
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.ChernCancel

/-! # Chern Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The original fiber transport pulls back the genuine restricted
line-bundle Chern classes on a constructed open neighborhood. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.exists_native_chern_transport
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left))
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G).left) :
    let P := fun z => present (Intrinsic.FamilyFrames.familyChartParameter C z)
    ∃ U : Set (Intrinsic.FamilyFrames.FamilyChartBase C), IsOpen U ∧ Intrinsic.FamilyFrames.familyChartCenter C ∈ U ∧
      ∃ (hU : U ⊆ F.neighborhood) (hN : U ⊆ C.charts.charts.neighborhood),
        ∀ z : U, Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberChern (C := C) (Intrinsic.FamilyFrames.familyChartCenter C) (P (Intrinsic.FamilyFrames.familyChartCenter C)) L =
          AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
            (F.nativePointTransport z (hU z.property) (hN z.property) (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z)) 2
            (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberChern (C := C) z (P z) L) := by
  let P := fun z => present (Intrinsic.FamilyFrames.familyChartParameter C z)
  obtain ⟨ε, hε, hB, hchern⟩ := F.exists_constant_native_chern_class present L
  let U := Metric.ball (Intrinsic.FamilyFrames.familyChartCenter C) ε ∩ C.charts.charts.neighborhood
  have hU : U ⊆ F.neighborhood := fun _ hz => hB hz.1
  have hN : U ⊆ C.charts.charts.neighborhood := Set.inter_subset_right
  refine ⟨U, Metric.isOpen_ball.inter C.charts.charts.isOpen,
    ⟨Metric.mem_ball_self hε, Family.ChartOpenImage.familyChartCenter_mem C⟩, hU, hN, ?_⟩
  intro z
  exact F.cancel_central_chern_comparison z (hU z.property) (hN z.property)
    (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z) _ _ (hchern ⟨z.val, z.property.1⟩)

end

end OAI.RepresentationTheory.Theta.Geometric
