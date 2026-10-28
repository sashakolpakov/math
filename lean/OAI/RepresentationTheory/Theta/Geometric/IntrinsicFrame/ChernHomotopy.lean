import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.TorusHomotopy
import OAI.RepresentationTheory.Theta.Geometric.CocycleClassNaturality

/-! # Chern Homotopy -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! An actual algebraic line bundle on the total abelian family has
constant pulled-back Chern class on the constructed fixed torus. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.centralTorus_t2 (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)
    (present : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C))) :
    T2Space F.CentralTorus := by
  let : T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C (Intrinsic.FamilyFrames.familyChartCenter C)) := present.t2Space
  exact (F.centralTorusHomeomorph present).isEmbedding.t2Space

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.exists_constant_line_chern_class
    (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left))
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G).left) :
    let P := present (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))
    let : CompactSpace F.CentralTorus := F.centralTorus_compact P
    let : T2Space F.CentralTorus := F.centralTorus_t2 P
    let cocycle := (SchemeLineFrame.schemeLineAtlas L).continuousCocycle (X := ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G)
    ∃ (ε : ℝ) (hε : 0 < ε) (hB : Metric.ball (Intrinsic.FamilyFrames.familyChartCenter C) ε ⊆ F.neighborhood)
      (family : C(Metric.ball (Intrinsic.FamilyFrames.familyChartCenter C) ε × F.CentralTorus,
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G))),
      (∀ p, family p = F.centralTorusFamilyMap (Metric.ball (Intrinsic.FamilyFrames.familyChartCenter C) ε) hB p) ∧
      ∀ z : Metric.ball (Intrinsic.FamilyFrames.familyChartCenter C) ε,
        (cocycle.pullback (TopCat.ofHom
          (Family.Homotopy.continuousFamilySlice family ⟨Intrinsic.FamilyFrames.familyChartCenter C, Metric.mem_ball_self hε⟩))).chernClass =
        (cocycle.pullback (TopCat.ofHom (Family.Homotopy.continuousFamilySlice family z))).chernClass := by
  let P := present (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))
  let : CompactSpace F.CentralTorus := F.centralTorus_compact P
  let : T2Space F.CentralTorus := F.centralTorus_t2 P
  obtain ⟨ε, hε, hB, family, hfamily, hhom⟩ := F.exists_ball_torus_homotopy present
  refine ⟨ε, hε, hB, family, hfamily, ?_⟩
  intro z
  exact ((SchemeLineFrame.schemeLineAtlas L).continuousCocycle (X := ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G)).chernClass_homotopic_compact_source
    (TopCat.ofHom (Family.Homotopy.continuousFamilySlice family ⟨Intrinsic.FamilyFrames.familyChartCenter C, Metric.mem_ball_self hε⟩))
    (TopCat.ofHom (Family.Homotopy.continuousFamilySlice family z)) (hhom z)

end

end OAI.RepresentationTheory.Theta.Geometric
