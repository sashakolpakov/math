import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.TorusMap
import OAI.RepresentationTheory.Theta.Geometric.Family.Homotopy
import Mathlib.Analysis.Convex.PathConnected

/-! # Torus Homotopy -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! On a constructed ball in the actual base chart, the fixed central
torus maps into the total family by mutually homotopic continuous maps. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.exists_ball_torus_homotopy
    (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left)) :
    ∃ (ε : ℝ) (hε : 0 < ε) (hB : Metric.ball (Intrinsic.FamilyFrames.familyChartCenter C) ε ⊆ F.neighborhood)
      (family : C(Metric.ball (Intrinsic.FamilyFrames.familyChartCenter C) ε × F.CentralTorus,
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G))),
      (∀ p, family p = F.centralTorusFamilyMap (Metric.ball (Intrinsic.FamilyFrames.familyChartCenter C) ε) hB p) ∧
      ∀ z : Metric.ball (Intrinsic.FamilyFrames.familyChartCenter C) ε,
        (Family.Homotopy.continuousFamilySlice family ⟨Intrinsic.FamilyFrames.familyChartCenter C, Metric.mem_ball_self hε⟩).Homotopic
          (Family.Homotopy.continuousFamilySlice family z) := by
  obtain ⟨U, hU, hUopen, hxU, hcont⟩ := F.exists_continuous_centralTorusFamily present
  obtain ⟨ε, hε, hBU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hxU)
  let B := Metric.ball (Intrinsic.FamilyFrames.familyChartCenter C) ε
  have hB : B ⊆ F.neighborhood := hBU.trans hU
  let includeBase : B → U := fun z => ⟨z.val, hBU z.property⟩
  have hi : Continuous includeBase := continuous_subtype_val.subtype_mk _
  let family : C(B × F.CentralTorus, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G)) :=
    ⟨fun p => F.centralTorusFamilyMap U hU (includeBase p.1, p.2),
      hcont.comp (hi.prodMap continuous_id)⟩
  refine ⟨ε, hε, hB, family, fun _ => rfl, ?_⟩
  let : PathConnectedSpace B := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_ball (Intrinsic.FamilyFrames.familyChartCenter C) ε).isPathConnected
      ⟨Intrinsic.FamilyFrames.familyChartCenter C, Metric.mem_ball_self hε⟩)
  intro z
  exact Family.Homotopy.continuousFamily_homotopic family
    (PathConnectedSpace.somePath ⟨Intrinsic.FamilyFrames.familyChartCenter C, Metric.mem_ball_self hε⟩ z)

end

end OAI.RepresentationTheory.Theta.Geometric
