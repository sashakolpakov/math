import OAI.RepresentationTheory.Theta.Geometric.Family.ChartOpenImage
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicTorsionRigidity
import OAI.ArithmeticGeometry.Descent.CMVariety.FamilyLevelPeriods

/-! # Frame Level -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The original full level has fixed divided-period coordinates in
the constructed holomorphic integral frame near its central fiber. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff _root_.Topology _root_.CategoryTheory.MonObj

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

local instance IntrinsicFrame.FrameLevel.nativeFrameFullLevel_nativeRealLieGroup (z : Intrinsic.FamilyFrames.FamilyChartBase C) [IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left] :
    LieGroup (𝓘(ℝ, Intrinsic.FamilyFrames.FamilyChartModel C z)) ∞ (Intrinsic.FamilyFrames.FamilyChartPoints C z) :=
  ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (Intrinsic.FamilyFrames.familyChartFiber C z).scheme

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.fullLevel_coordinates
    (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left))
    (N : ℕ) (hN : 0 < N) (level : G.FullLevel N) :
    let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
    let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
    ∃ coordinates : Multiplicative (Fin (2 * g) → ZMod N) → Fin F.rank → ℤ,
      ∀ᶠ z in 𝓝 (Intrinsic.FamilyFrames.familyChartCenter C), ∀ a,
        ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z)
          ((N : ℝ)⁻¹ • F.periods z (fun i => (coordinates a i : ℝ))) =
          ((level.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left).hom.app (.op (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))
            (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a)).val := by
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
  let : ConnectedSpace (Intrinsic.FamilyFrames.FamilyChartPoints C (Intrinsic.FamilyFrames.familyChartCenter C)) :=
    (present (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))).connectedSpace
  have hc := F.chartData (Intrinsic.FamilyFrames.familyChartCenter C) (Family.ChartOpenImage.familyChartCenter_mem C)
  have hsurj := ArithmeticGeometry.Descent.CMVariety.ChartTorsionReferences.Abelian.chartExponential_surjective (E := Intrinsic.FamilyFrames.FamilyChartModel C (Intrinsic.FamilyFrames.familyChartCenter C))
    (F.charts (Intrinsic.FamilyFrames.familyChartCenter C)) hc.2.2.1 hc.1 hc.2.1
  have hb : ∀ᶠ z in 𝓝 (Intrinsic.FamilyFrames.familyChartCenter C),
      ∃ b : Module.Basis (Fin F.rank) ℤ
          (ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z)),
        ∀ i, (b i : Intrinsic.FamilyFrames.FamilyChartTangent C) = F.periods z (Pi.single i 1) :=
    Filter.Eventually.mono (F.isOpen.mem_nhds F.center) (fun z hz => F.full z hz)
  apply ArithmeticGeometry.Descent.CMVariety.FamilyLevelPeriods.Abelian.FamilyPoints.exists_family_level_period_coordinates G (Intrinsic.FamilyFrames.familyChartParameter C) (Intrinsic.FamilyFrames.familyChartCenter C)
    (fun z => ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z)) F.exponentialFamily hsurj
    (fun z => ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z))
    (fun z => ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.mem_chartPeriodLattice (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z))
    (fun z => (F.periods z).toContinuousLinearMap)
    (F.continuous.continuousAt (F.isOpen.mem_nhds F.center)) (by
      filter_upwards [hb] with z hz
      obtain ⟨b, hbp⟩ := hz
      refine ⟨b, fun j => (hbp j).trans ?_⟩
      apply congrArg (F.periods z)
      funext i
      simp [Pi.single_apply]) N hN level
  have h := ArithmeticGeometry.Descent.CMVariety.IntrinsicTorsionRigidity.Abelian.FamilyPoints.native_torsion_section_locally_one G present C.charts.affineOpen C.charts.isAffine
    C.openMap C.charts.projection_eq C.charts.sectionAlgebra C.charts.section_eq C.charts.charts N hN
  have heq : (C.point.comp C.charts.sectionAlgebra).comp
      (IsScalarTower.toAlgHom ℂ C.algebra
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) C.charts.affineOpen)) = C.point := by
    rw [AlgHom.comp_assoc, C.charts.retraction, AlgHom.comp_id]
  rw [heq] at h
  exact h

end

end OAI.RepresentationTheory.Theta.Geometric
