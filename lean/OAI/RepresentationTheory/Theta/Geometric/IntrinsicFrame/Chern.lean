import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.ChernHomotopy
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.TorusMap
import OAI.RepresentationTheory.Theta.Geometric.SchemeChernHomotopy

/-! # Chern -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The constructed real period frame preserves the original native
Chern classes of the actual restrictions of every total-family line bundle. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.exists_constant_native_chern_class
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left))
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G).left) :
    let P := fun z => present (Intrinsic.FamilyFrames.familyChartParameter C z)
    ∃ (ε : ℝ) (_hε : 0 < ε) (hB : Metric.ball (Intrinsic.FamilyFrames.familyChartCenter C) ε ⊆ F.neighborhood),
      ∀ z : Metric.ball (Intrinsic.FamilyFrames.familyChartCenter C) ε,
        AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
            (TopCat.ofHom (F.presentedTorusMap (Intrinsic.FamilyFrames.familyChartCenter C) F.center
              (P (Intrinsic.FamilyFrames.familyChartCenter C)))) 2
            (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass (P (Intrinsic.FamilyFrames.familyChartCenter C)).variety.variety.presentation
              (L.pullback (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberInclusion (C := C) (Intrinsic.FamilyFrames.familyChartCenter C)
                (P (Intrinsic.FamilyFrames.familyChartCenter C))).left)) =
          AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
            (TopCat.ofHom (F.presentedTorusMap z (hB z.property) (P z))) 2
            (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass (P z).variety.variety.presentation
              (L.pullback (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberInclusion (C := C) z (P z)).left)) := by
  let P := fun z => present (Intrinsic.FamilyFrames.familyChartParameter C z)
  let : CompactSpace F.CentralTorus := F.centralTorus_compact (P (Intrinsic.FamilyFrames.familyChartCenter C))
  let : T2Space F.CentralTorus := F.centralTorus_t2 (P (Intrinsic.FamilyFrames.familyChartCenter C))
  obtain ⟨ε, hε, hB, family, hfamily, hhom⟩ := F.exists_ball_torus_homotopy present
  refine ⟨ε, hε, hB, ?_⟩
  intro z
  have hs (w : Metric.ball (Intrinsic.FamilyFrames.familyChartCenter C) ε) :
      (TopCat.ofHom (F.presentedTorusMap w (hB w.property) (P w)) ≫
        TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberInclusion (C := C) w (P w)))).hom =
        Family.Homotopy.continuousFamilySlice family w := by
    apply ContinuousMap.ext
    intro v
    exact (F.presentedTorusMap_family _ hB w (P w) v).trans (hfamily (w, v)).symm
  apply SchemeChernHomotopy.native_chernClass_eq_of_homotopic (L := L)
    (P (Intrinsic.FamilyFrames.familyChartCenter C)).variety.variety.presentation (P z).variety.variety.presentation
    (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberInclusion (C := C) (Intrinsic.FamilyFrames.familyChartCenter C) (P (Intrinsic.FamilyFrames.familyChartCenter C)))
    (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberInclusion (C := C) z (P z))
    (TopCat.ofHom (F.presentedTorusMap (Intrinsic.FamilyFrames.familyChartCenter C) F.center (P (Intrinsic.FamilyFrames.familyChartCenter C))))
    (TopCat.ofHom (F.presentedTorusMap z (hB z.property) (P z)))
  rw [hs ⟨Intrinsic.FamilyFrames.familyChartCenter C, Metric.mem_ball_self hε⟩, hs z]
  exact hhom z

end

end OAI.RepresentationTheory.Theta.Geometric
