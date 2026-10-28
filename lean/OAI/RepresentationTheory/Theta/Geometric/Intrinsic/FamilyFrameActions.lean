import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames
import OAI.RepresentationTheory.Theta.Geometric.MovingLatticeAction
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.ChartLatticeAction
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFamilyEndomorphismDerivative

/-! # Family Frame Actions -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrameActions

noncomputable section

/-! The actual family endomorphisms have locally constant integer
matrices in the constructed full holomorphic period frame. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff _root_.Topology _root_.CategoryTheory.MonObj

open OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFamilyEndomorphismDerivative.Abelian.RelativeCharts

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

local instance (z : FamilyFrames.FamilyChartBase C) [IsIntegral (FamilyFrames.familyChartFiber C z).scheme.left] :
    LieGroup (𝓘(ℝ, FamilyFrames.FamilyChartModel C z)) ∞ (FamilyFrames.FamilyChartPoints C z) :=
  ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (FamilyFrames.familyChartFiber C z).scheme

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.continuous_endomorphism_derivative
    (F : FamilyFrames.NativeFamilyPeriodFrame C) (k : G.scheme ⟶ G.scheme) [IsMonHom k] :
    let : ∀ z : FamilyFrames.FamilyChartBase C, IsIntegral (FamilyFrames.familyChartFiber C z).scheme.left := F.integral
    ∃ (U : Set (FamilyFrames.FamilyChartBase C))
      (D : FamilyFrames.FamilyChartBase C → FamilyFrames.FamilyChartTangent C →L[ℝ] FamilyFrames.FamilyChartTangent C),
      IsOpen U ∧ FamilyFrames.familyChartCenter C ∈ U ∧ U ⊆ C.charts.charts.neighborhood ∧ ContinuousOn D U ∧
      ∀ z ∈ U, ∀ v,
        ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := FamilyFrames.FamilyChartModel C z) (F.charts z) (D z v) =
          mfderiv (𝓘(ℝ, FamilyFrames.FamilyChartModel C z)) (𝓘(ℝ, FamilyFrames.FamilyChartModel C z))
            (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k (FamilyFrames.familyChartParameter C z))) 1
            (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := FamilyFrames.FamilyChartModel C z) (F.charts z) v) := by
  let : ∀ z : FamilyFrames.FamilyChartBase C, IsIntegral (FamilyFrames.familyChartFiber C z).scheme.left := F.integral
  let A := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) C.charts.affineOpen
  let i := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) C.charts.affineOpen C.charts.isAffine
  let N := C.charts.charts
  let y := C.point.comp C.charts.sectionAlgebra
  have hx : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i y =
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i y ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.identitySection S G := by
    have he := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap A C.algebra C.charts.sectionAlgebra i
      (y.comp (IsScalarTower.toAlgHom ℂ C.algebra A))
    have hy : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap C.charts.sectionAlgebra
        (y.comp (IsScalarTower.toAlgHom ℂ C.algebra A)) = y := N.onSection
    rw [C.charts.section_eq, hy, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp] at he
    have hp := ArithmeticGeometry.Descent.CMVariety.FiberChartProjection.Abelian.RelativeCharts.nativeAffinePoint_base (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) C.openMap i C.charts.projection_eq y
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i y ≫ ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G = _ at hp
    rw [hp]
    exact he.symm
  obtain ⟨U₁, D, hU₁, hx₁, hsub₁, hD, hDc⟩ :=
    ArithmeticGeometry.Descent.CMVariety.IntrinsicFamilyEndomorphismDerivative.Abelian.RelativeCharts.exists_continuous_native_familyEndomorphism_derivative G k i N hx
      (FamilyFrames.familyChartParameter C) F.charts (by
        intro z hz
        obtain ⟨h1, h0, hmd, hsrc, htgt, hf, hi, _, _⟩ := F.chartData z hz
        exact ⟨h1, h0, hmd, hsrc, htgt, hf, hi⟩)
  have hx₁' : FamilyFrames.familyChartCenter C ∈ U₁ := by
    simpa only [FamilyFrames.familyChartCenter, N, y, AlgHom.comp_assoc, C.charts.retraction, AlgHom.comp_id] using hx₁
  exact ⟨U₁, D, hU₁, hx₁', hsub₁, hD, hDc⟩

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.endomorphism_matrices_locally_constant
    (F : FamilyFrames.NativeFamilyPeriodFrame C) (k : G.scheme ⟶ G.scheme) [IsMonHom k] :
    let : ∀ z : FamilyFrames.FamilyChartBase C, IsIntegral (FamilyFrames.familyChartFiber C z).scheme.left := F.integral
    ∃ (U : Set (FamilyFrames.FamilyChartBase C))
      (D : FamilyFrames.FamilyChartBase C → FamilyFrames.FamilyChartTangent C →L[ℝ] FamilyFrames.FamilyChartTangent C),
      IsOpen U ∧ FamilyFrames.familyChartCenter C ∈ U ∧ U ⊆ F.neighborhood ∧ ContinuousOn D U ∧
      (∀ z ∈ U, ∀ v,
        ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := FamilyFrames.FamilyChartModel C z) (F.charts z) (D z v) =
          mfderiv (𝓘(ℝ, FamilyFrames.FamilyChartModel C z)) (𝓘(ℝ, FamilyFrames.FamilyChartModel C z))
            (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k (FamilyFrames.familyChartParameter C z))) 1
            (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := FamilyFrames.FamilyChartModel C z) (F.charts z) v)) ∧
      ∀ z ∈ U, ∀ v : Fin F.rank → ℝ,
        (F.periods z).symm (D z (F.periods z v)) =
          (F.periods (FamilyFrames.familyChartCenter C)).symm
            (D (FamilyFrames.familyChartCenter C) (F.periods (FamilyFrames.familyChartCenter C) v)) := by
  let : ∀ z : FamilyFrames.FamilyChartBase C, IsIntegral (FamilyFrames.familyChartFiber C z).scheme.left := F.integral
  let : ∀ z : FamilyFrames.FamilyChartBase C, T2Space (FamilyFrames.FamilyChartPoints C z) := F.t2
  obtain ⟨U₁, D, hU₁, hx₁', _, hD, hDc⟩ := F.continuous_endomorphism_derivative k
  let U₀ := F.neighborhood ∩ U₁
  have hU₀ : IsOpen U₀ := F.isOpen.inter hU₁
  let z₀ : U₀ := ⟨FamilyFrames.familyChartCenter C, F.center, hx₁'⟩
  let Λ := fun z : U₀ => ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (E := FamilyFrames.FamilyChartModel C z) (F.charts z)
  choose b hb using fun z : U₀ => F.full z z.property.1
  have hpres (z : U₀) (v : FamilyFrames.FamilyChartTangent C) (hv : v ∈ Λ z) : D z v ∈ Λ z := by
    let K := ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k (FamilyFrames.familyChartParameter C z)
    let : IsMonHom K := ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism_group S G k (FamilyFrames.familyChartParameter C z)
    exact ChartLatticeAction.nativeChartDerivative_preserves_lattice (FamilyFrames.familyChartFiber C z) (F.charts z) K
      (D z) (hDc z z.property.2) v hv
  have hr₀ : ContinuousAt (fun z : U₀ => (F.periods z).toContinuousLinearMap) z₀ :=
    ContinuousAt.comp (f := fun z : U₀ => z.val) (x := z₀)
      (F.continuous.continuousAt (F.isOpen.mem_nhds F.center)) continuous_subtype_val.continuousAt
  have hD₀ : ContinuousAt (fun z : U₀ => D z) z₀ :=
    ContinuousAt.comp (f := fun z : U₀ => z.val) (x := z₀)
      (hD.continuousAt (hU₁.mem_nhds hx₁')) continuous_subtype_val.continuousAt
  have hconstant := MovingLatticeAction.movingLatticeAction_locally_constant Λ b (fun z : U₀ => F.periods z) hb
    (fun z : U₀ => D z) hpres z₀ hr₀ hD₀
  have hevent : ∀ᶠ z in 𝓝 (FamilyFrames.familyChartCenter C),
      z ∈ U₀ ∧ ∀ v : Fin F.rank → ℝ,
        (F.periods z).symm (D z (F.periods z v)) =
          (F.periods (FamilyFrames.familyChartCenter C)).symm
            (D (FamilyFrames.familyChartCenter C) (F.periods (FamilyFrames.familyChartCenter C) v)) := by
    rw [← hU₀.isOpenEmbedding_subtypeVal.map_nhds_eq z₀]
    change ∀ᶠ z : U₀ in 𝓝 z₀, _
    exact hconstant.mono (fun z hz => ⟨z.property, hz⟩)
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hevent
  refine ⟨U, D, hU, hxU, fun z hz => (hUsub hz).1.1,
    hD.mono (fun z hz => (hUsub hz).1.2), ?_, ?_⟩
  · exact fun z hz => hDc z (hUsub hz).1.2
  · exact fun z hz => (hUsub hz).2

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrameActions
