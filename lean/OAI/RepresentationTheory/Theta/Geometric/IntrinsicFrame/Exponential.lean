import OAI.RepresentationTheory.Theta.Geometric.Family.ChartOpenImage
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicExponentialOn

/-! # Exponential -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Joint continuity of the actual total-family exponential in the
same holomorphic period frame used for the integral action and level. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff _root_.Topology

theorem IntrinsicFrame.Exponential.chartTangentMap_eq_of_inverse_near_zero
    {E V G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace G] [ChartedSpace E G] [CommGroup G]
    (c d : OpenPartialHomeomorph G V) (U : Set V) (hU : IsOpen U) (h0 : (0 : V) ∈ U)
    (h : ∀ v ∈ U, c.symm v = d.symm v) :
    ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := E) c = ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := E) d := by
  have he : (c.symm : V → G) =ᶠ[𝓝 (0 : V)] d.symm :=
    Filter.Eventually.mono (hU.mem_nhds h0) h
  exact he.mfderiv_eq

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

local instance IntrinsicFrame.Exponential.nativeFrameExponential_nativeRealLieGroup (z : Intrinsic.FamilyFrames.FamilyChartBase C) [IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left] :
    LieGroup (𝓘(ℝ, Intrinsic.FamilyFrames.FamilyChartModel C z)) ∞ (Intrinsic.FamilyFrames.FamilyChartPoints C z) :=
  ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (Intrinsic.FamilyFrames.familyChartFiber C z).scheme

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.tangentMap_eq
    (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C) (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ C.charts.charts.neighborhood) :
    let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
    ∀ c : OpenPartialHomeomorph (Intrinsic.FamilyFrames.FamilyChartPoints C z) (Intrinsic.FamilyFrames.FamilyChartTangent C),
      c.target = (F.charts z).target →
      (∀ v ∈ c.target,
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (Intrinsic.FamilyFrames.familyChartParameter C z)) (c.symm v) =
          AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (Intrinsic.FamilyFrames.familyChartParameter C z)) ((F.charts z).symm v)) →
      ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z) =
        ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := Intrinsic.FamilyFrames.FamilyChartModel C z) c := by
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
  dsimp only
  intro c ht hi
  obtain ⟨h1, h0, _⟩ := F.chartData z hz
  apply IntrinsicFrame.Exponential.chartTangentMap_eq_of_inverse_near_zero (F.charts z) c
    (F.charts z).target (F.charts z).open_target (h0 ▸ (F.charts z).map_source h1)
  intro v hv
  apply F.exponentialFamily.inclusion z
  exact (hi v (ht.symm ▸ hv)).symm

theorem IntrinsicFrame.Exponential.exists_continuous_family_chart_exponential
    [∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left]
    [∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z)]
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left)) :
    ∃ (c : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, OpenPartialHomeomorph (Intrinsic.FamilyFrames.FamilyChartPoints C z) (Intrinsic.FamilyFrames.FamilyChartTangent C))
      (B : Set (Intrinsic.FamilyFrames.FamilyChartBase C)), IsOpen B ∧ Intrinsic.FamilyFrames.familyChartCenter C ∈ B ∧
      B ⊆ C.charts.charts.neighborhood ∧
      ContinuousOn (fun z : Intrinsic.FamilyFrames.FamilyChartBase C × Intrinsic.FamilyFrames.FamilyChartTangent C =>
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (Intrinsic.FamilyFrames.familyChartParameter C z.1))
          (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (G := Intrinsic.FamilyFrames.FamilyChartPoints C z.1) (E := Intrinsic.FamilyFrames.FamilyChartModel C z.1) (c z.1) z.2))
          (B ×ˢ Set.univ) ∧
      ∀ z ∈ B,
        (c z).target = {v | (z,v) ∈ C.charts.charts.charts.total.target} ∧
        ∀ v ∈ (c z).target,
          AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (Intrinsic.FamilyFrames.familyChartParameter C z)) ((c z).symm v) =
            (ArithmeticGeometry.Descent.CMVariety.AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart
              (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) C.charts.affineOpen)
              (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.total S G) C.charts.affineOpen C.charts.isAffine)
              C.charts.charts.charts.total).symm (z,v) := by
  obtain ⟨c₀, hc, ⟨B, hB, hxB, hBN, hcont, _, _⟩, _⟩ :=
    AlgebraicGeometry.PELModuli.CMPoints.IntrinsicHolomorphicExponentialOn.IntrinsicFamilyPeriods.exists_native_holomorphic_exponential_on G present
      C.charts.affineOpen C.charts.isAffine C.openMap C.charts.projection_eq
      C.charts.sectionAlgebra C.charts.section_eq C.charts.charts
  have hxB' : Intrinsic.FamilyFrames.familyChartCenter C ∈ B := by
    simpa only [Intrinsic.FamilyFrames.familyChartCenter, AlgHom.comp_assoc, C.charts.retraction, AlgHom.comp_id] using hxB
  refine ⟨c₀, B, hB, hxB', hBN, hcont, ?_⟩
  intro z hz
  obtain ⟨_, _, _, _, ht, _, hi⟩ := hc z (hBN hz)
  exact ⟨ht, hi⟩

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.continuous_exponential
    (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left)) :
    let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
    let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
    ∃ U : Set (Intrinsic.FamilyFrames.FamilyChartBase C), IsOpen U ∧ Intrinsic.FamilyFrames.familyChartCenter C ∈ U ∧
      U ⊆ F.neighborhood ∧
      ContinuousOn (fun z : Intrinsic.FamilyFrames.FamilyChartBase C × Intrinsic.FamilyFrames.FamilyChartTangent C =>
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.fiberInclusion (ArithmeticGeometry.Descent.CMVariety.AbelianFamilyPoints.FamilyPoints.projection S G) (Intrinsic.FamilyFrames.familyChartParameter C z.1))
          (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (G := Intrinsic.FamilyFrames.FamilyChartPoints C z.1) (E := Intrinsic.FamilyFrames.FamilyChartModel C z.1) (F.charts z.1) z.2)) (U ×ˢ Set.univ) := by
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
  obtain ⟨c, B, hB, hxB', hBN, hcont, hc⟩ := IntrinsicFrame.Exponential.exists_continuous_family_chart_exponential (C := C) present
  have hmaps (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ B) :
      ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z) =
        ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (c z) := by
    obtain ⟨_, _, _, _, ht, _, hi, _, _⟩ := F.chartData z (hBN hz)
    obtain ⟨ht', hi'⟩ := hc z hz
    have htargets : (c z).target = (F.charts z).target := ht'.trans ht.symm
    apply F.tangentMap_eq z (hBN hz) (c z) htargets
    intro v hv
    exact (hi' v hv).trans (hi v (htargets ▸ hv)).symm
  refine ⟨F.neighborhood ∩ B, F.isOpen.inter hB, ⟨F.center, hxB'⟩,
    Set.inter_subset_left, ?_⟩
  apply (hcont.mono (fun z hz => ⟨hz.1.2, hz.2⟩)).congr
  intro z hz
  change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map _
    (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := Intrinsic.FamilyFrames.FamilyChartPoints C z.1)
      (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := Intrinsic.FamilyFrames.FamilyChartModel C z.1) (F.charts z.1) z.2)) = _
  rw [hmaps z.1 hz.1.2]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric
