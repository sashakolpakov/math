import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicPeriods

/-! # Family Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames

noncomputable section

/-! Full holomorphic period frames of an actual abelian scheme, retaining
the relative identity charts and the actual family exponential. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} (C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x)

abbrev FamilyChartBase := AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates C.presentation.presentation.map → ℂ
abbrev FamilyChartTangent := AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates C.charts.relativePresentation.presentation.map → ℂ

def familyChartParameter (z : FamilyChartBase C) : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S :=
  AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap C.algebra C.openMap (C.charts.charts.charts.base.symm z)

def familyChartCenter : FamilyChartBase C := C.charts.charts.charts.base C.point

abbrev familyChartFiber (z : FamilyChartBase C) := G.pullback (familyChartParameter C z).left
abbrev FamilyChartPoints (z : FamilyChartBase C) := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (familyChartFiber C z).scheme
abbrev FamilyChartModel (z : FamilyChartBase C) [IsIntegral (familyChartFiber C z).scheme.left] :=
  Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (familyChartFiber C z).scheme.hom) → ℂ

local instance (z : FamilyChartBase C) [IsIntegral (familyChartFiber C z).scheme.left] :
    LieGroup (𝓘(ℝ, FamilyChartModel C z)) ∞ (FamilyChartPoints C z) :=
  ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (familyChartFiber C z).scheme

structure NativeFamilyPeriodFrame where
  [integral : ∀ z : FamilyChartBase C, IsIntegral (familyChartFiber C z).scheme.left]
  [t2 : ∀ z : FamilyChartBase C, T2Space (FamilyChartPoints C z)]
  charts : ∀ z : FamilyChartBase C, OpenPartialHomeomorph (FamilyChartPoints C z) (FamilyChartTangent C)
  rank : ℕ
  periods : FamilyChartBase C → (Fin rank → ℝ) ≃L[ℝ] FamilyChartTangent C
  chartData : ArithmeticGeometry.Descent.CMVariety.FamilyChartData.Abelian.FamilyIdentityChartData (fun z => FamilyChartModel C z) (FamilyChartPoints C) charts
    (fun z y => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (familyChartParameter C z)) y)
    (ArithmeticGeometry.Descent.CMVariety.AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) C.charts.affineOpen)
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) C.charts.affineOpen C.charts.isAffine)
      C.charts.charts.charts.total) C.charts.charts.neighborhood
  exponentialFamily : ArithmeticGeometry.Descent.CMVariety.LocalPeriod.Abelian.LocalPeriodFamily (FamilyChartPoints C)
    (fun z => ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := FamilyChartModel C z) (charts z))
    (fun z y => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (familyChartParameter C z)) y)
    (familyChartCenter C)
  neighborhood : Set (FamilyChartBase C)
  isOpen : IsOpen neighborhood
  center : familyChartCenter C ∈ neighborhood
  continuous : ContinuousOn (fun z => (periods z).toContinuousLinearMap) neighborhood
  holomorphic : ∀ i, DifferentiableOn ℂ (fun z => periods z (Pi.single i 1)) neighborhood
  full : ∀ z ∈ neighborhood, ∃ b : Module.Basis (Fin rank) ℤ (ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (E := FamilyChartModel C z) (charts z)),
    ∀ i, (b i : FamilyChartTangent C) = periods z (Pi.single i 1)

theorem exists_nativeFamilyPeriodFrame
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left)) :
    Nonempty (NativeFamilyPeriodFrame C) := by
  let (z : FamilyChartBase C) : IsIntegral (familyChartFiber C z).scheme.left :=
    (present (familyChartParameter C z)).isIntegral
  let (z : FamilyChartBase C) : T2Space (FamilyChartPoints C z) :=
    (present (familyChartParameter C z)).t2Space
  have h := AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicPeriods.IntrinsicFamilyPeriods.exists_native_holomorphic_full_period_bases
    (E := FamilyChartTangent C) (F := FamilyChartBase C) G present
    C.charts.affineOpen C.charts.isAffine C.openMap C.charts.projection_eq
    C.charts.sectionAlgebra C.charts.section_eq C.charts.charts
  simp only [AlgHom.comp_assoc, C.charts.retraction, AlgHom.comp_id] at h
  obtain ⟨c, n, r, hc, he, U, hU, hx, hr, hhol, hb⟩ := h
  exact ⟨{
    charts := c
    rank := n
    periods := r
    chartData := hc
    exponentialFamily := he
    neighborhood := U
    isOpen := hU
    center := hx
    continuous := hr
    holomorphic := hhol
    full := hb }⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames
