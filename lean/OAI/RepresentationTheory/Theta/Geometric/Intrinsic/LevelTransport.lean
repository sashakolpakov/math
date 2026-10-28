import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.LevelTransport
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.EndomorphismTransport

/-! # Level Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic

noncomputable section

/-! The original native fiber transport preserves every label of the
same original full level, after the literal fiber presentation maps. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}

def LevelTransport.presentedFullLevelPoint {N : ℕ} (level : G.FullLevel N) (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left))
    (a : Multiplicative (Fin (2 * g) → ZMod N)) : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.variety.toOver :=
  AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom (IntrinsicFrame.LevelTransport.familyFullLevelPoint level y a)

variable {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : FamilyFrames.NativeFamilyPeriodFrame C)

theorem FamilyFrames.NativeFamilyPeriodFrame.exists_native_full_level_transport
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left))
    (N : ℕ) (hlevel : 0 < N) (level : G.FullLevel N) :
    let P := fun z => present (FamilyFrames.familyChartParameter C z)
    ∃ U : Set (FamilyFrames.FamilyChartBase C), IsOpen U ∧ FamilyFrames.familyChartCenter C ∈ U ∧
      ∃ (hU : U ⊆ F.neighborhood) (hN : U ⊆ C.charts.charts.neighborhood),
        ∀ (z : U) (a : Multiplicative (Fin (2 * g) → ZMod N)),
          F.nativeFiberTransport z (hU z.property) (hN z.property) (P (FamilyFrames.familyChartCenter C)) (P z)
            (LevelTransport.presentedFullLevelPoint level (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C))
              (P (FamilyFrames.familyChartCenter C)) a) =
            LevelTransport.presentedFullLevelPoint level (FamilyFrames.familyChartParameter C z) (P z) a := by
  let P := fun z => present (FamilyFrames.familyChartParameter C z)
  obtain ⟨V, hVopen, hxV, hV, hcomm⟩ := F.exists_level_torus_transport present N hlevel level
  let U := V ∩ C.charts.charts.neighborhood
  have hU : U ⊆ F.neighborhood := fun _ hz => hV hz.1
  have hN : U ⊆ C.charts.charts.neighborhood := Set.inter_subset_right
  refine ⟨U, hVopen.inter C.charts.charts.isOpen, ⟨hxV, Family.ChartOpenImage.familyChartCenter_mem C⟩, hU, hN, ?_⟩
  intro z a
  let t := (F.centralTorusHomeomorph (P (FamilyFrames.familyChartCenter C))).symm
    (IntrinsicFrame.LevelTransport.familyFullLevelPoint level (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)) a)
  have ht : F.presentedTorusMap (FamilyFrames.familyChartCenter C) F.center (P (FamilyFrames.familyChartCenter C)) t =
      LevelTransport.presentedFullLevelPoint level (FamilyFrames.familyChartParameter C (FamilyFrames.familyChartCenter C)) (P (FamilyFrames.familyChartCenter C)) a := by
    rw [F.presentedTorusMap_center]
    exact congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P (FamilyFrames.familyChartCenter C)).comparison.hom)
      ((F.centralTorusHomeomorph (P (FamilyFrames.familyChartCenter C))).apply_symm_apply _)
  rw [← ht, F.nativeFiberTransport_presented]
  exact congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P z).comparison.hom) (hcomm ⟨z.val, z.property.1⟩ a)

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic
