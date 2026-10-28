import OAI.AlgebraicGeometry.Comparison.Betti.Affine.SchemeStalkCenters
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SchemeStalkPullback
import OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.AffineCharts
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ClosedGermQuotient

/-! # Scheme Stalk Pullback Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.SchemeStalkPullbackNormalization

noncomputable section

/-! The actual scheme holomorphic stalk pullback is the original affine germ map in its actual affine charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.Affine.ClosedGermQuotient.AnalyticLocal

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (φ : X ⟶ Y)
  (V : Y.left.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen (φ.left ⁻¹ᵁ V))
  (e : OpenPartialHomeomorph
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X (φ.left ⁻¹ᵁ V))) (RegularSmoothness.NativeModel X))
  (f : OpenPartialHomeomorph
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V)) (RegularSmoothness.NativeModel Y))
  (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X (φ.left ⁻¹ᵁ V))
    (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom))
  (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V)
    (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom))
  (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X (φ.left ⁻¹ᵁ V)))
  (hx : x ∈ e.source) (hfx : x.comp (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V) ∈ f.source)

private abbrev nativeInverseImageOpen : X.left.Opens := φ.left ⁻¹ᵁ V

local notation "pointX" => OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X
  (nativeInverseImageOpen φ V) hW x
local notation "chartX" => OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X
  (nativeInverseImageOpen φ V))
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X
    (nativeInverseImageOpen φ V) hW) e
local notation "chartY" => OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y V)
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y V hV) f

theorem affineSchemeChartStalkEquiv_pullback
    (a : ConcreteHolomorphicStalkMap.analyticHolomorphicStalk Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ pointX)) :
    SchemeStalkCenters.affineSchemeChartStalkEquivAt X (φ.left ⁻¹ᵁ V) hW e he x hx pointX rfl
      (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback φ pointX a) =
    ClosedGermQuotient.AnalyticLocal.affineChartGermPullback (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V) e f he hf x hx hfx
      (SchemeStalkCenters.affineSchemeChartStalkEquivAt Y V hV f hf (x.comp (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V)) hfx
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ pointX) (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback_point_square φ V hV hW x) a) := by
  have heC : chartX ∈ atlas (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
    ⟨φ.left ⁻¹ᵁ V, hW, e, he, rfl⟩
  have hfC : chartY ∈ atlas (RegularSmoothness.NativeModel Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) := ⟨V, hV, f, hf, rfl⟩
  have hpC : pointX ∈ (chartX).source := ⟨x, hx, rfl⟩
  have hqC : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ pointX ∈ (chartY).source := by
    rw [ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback_point_square φ V hV hW x]
    exact ⟨x.comp (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V), hfx, rfl⟩
  have hecenter : chartX pointX = e x := ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_apply _ _ e x
  have hfcenter : chartY (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ pointX) =
      f (x.comp (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V)) := by
    rw [ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback_point_square φ V hV hW x]
    exact ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_apply _ _ f (x.comp (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V))
  have hnorm := Holomorphic.RingedStalkCharts.AnalyticLocal.chartStructureStalkEquivAt_pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ)
    (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map φ ∞) chartX heC chartY hfC pointX hpC hqC
    (e x) hecenter (f (x.comp (ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.nativeAffineOpenPullback φ V))) hfcenter
    (ClosedImmersion.AffineCharts.nativeAffineSchemeChartMap_contDiffAt φ V hV hW e f he hf x hx hfx) a
  erw [SchemeStalkCenters.affineSchemeChartStalkEquivAt_eq_chart, SchemeStalkCenters.affineSchemeChartStalkEquivAt_eq_chart]
  simp only [ClosedImmersion.AffineCharts.nativeAffineSchemeChartMap_eq] at hnorm
  exact hnorm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.SchemeStalkPullbackNormalization
