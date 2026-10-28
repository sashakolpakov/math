import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.FrameLevel
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.CentralIdentification

/-! # Level Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual fixed-torus transport preserves each original full-level
label, using its proved fixed divided-period coordinates. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff _root_.Topology _root_.CategoryTheory.MonObj

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}

def IntrinsicFrame.LevelTransport.familyFullLevelPoint {N : ℕ} (level : G.FullLevel N) (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (a : Multiplicative (Fin (2 * g) → ZMod N)) : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback y.left).scheme :=
  ((level.pullback y.left).hom.app (.op (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a)).val

variable {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

local instance IntrinsicFrame.LevelTransport.nativeFrameLevelTransport_nativeRealLieGroup (z : Intrinsic.FamilyFrames.FamilyChartBase C)
    [IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left] :
    LieGroup (𝓘(ℝ, Intrinsic.FamilyFrames.FamilyChartModel C z)) ∞ (Intrinsic.FamilyFrames.FamilyChartPoints C z) :=
  ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (Intrinsic.FamilyFrames.familyChartFiber C z).scheme

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.exists_level_torus_transport
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left))
    (N : ℕ) (hN : 0 < N) (level : G.FullLevel N) :
    let P₀ := present (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))
    ∃ U : Set (Intrinsic.FamilyFrames.FamilyChartBase C), IsOpen U ∧ Intrinsic.FamilyFrames.familyChartCenter C ∈ U ∧
      ∃ hU : U ⊆ F.neighborhood, ∀ (z : U) (a : Multiplicative (Fin (2 * g) → ZMod N)),
        F.torusFiberMap z (hU z.property)
          ((F.centralTorusHomeomorph P₀).symm
            (IntrinsicFrame.LevelTransport.familyFullLevelPoint level (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) a)) =
          IntrinsicFrame.LevelTransport.familyFullLevelPoint level (Intrinsic.FamilyFrames.familyChartParameter C z) a := by
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
  let P₀ := present (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))
  obtain ⟨coords, hcoords⟩ := F.fullLevel_coordinates present N hN level
  obtain ⟨U, hsub, hopen, hcenter⟩ := mem_nhds_iff.mp (Filter.Eventually.and (F.isOpen.mem_nhds F.center) hcoords)
  have hU : U ⊆ F.neighborhood := fun _ hz => (hsub hz).1
  refine ⟨U, hopen, hcenter, hU, ?_⟩
  intro z a
  let v := (N : ℝ)⁻¹ • F.periods (Intrinsic.FamilyFrames.familyChartCenter C) (fun i => (coords a i : ℝ))
  have hc : F.centralTorusHomeomorph P₀ (QuotientAddGroup.mk v) =
      IntrinsicFrame.LevelTransport.familyFullLevelPoint level (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) a := by
    rw [F.centralTorusHomeomorph_mk]
    exact (hsub hcenter).2 a
  rw [← hc, Homeomorph.symm_apply_apply]
  change (F.transportedExponential z v).toMul = _
  rw [F.transportedExponential_apply]
  have hv : F.realTransport z v = (N : ℝ)⁻¹ • F.periods z (fun i => (coords a i : ℝ)) := by
    rw [map_smul]
    apply congrArg ((N : ℝ)⁻¹ • ·)
    exact congrArg (F.periods z) ((F.periods (Intrinsic.FamilyFrames.familyChartCenter C)).symm_apply_apply _)
  rw [hv]
  exact (hsub z.property).2 a

end

end OAI.RepresentationTheory.Theta.Geometric
