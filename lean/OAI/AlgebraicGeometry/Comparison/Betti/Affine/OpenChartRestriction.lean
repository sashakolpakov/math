import OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenChartFormNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartModuleBases

/-! # Open Chart Restriction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenChartRestriction

noncomputable section

/-! Returning from affine coordinates gives the actual restriction to the corresponding manifold open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartModuleBases

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  (U : X.left.Opens) (hU : IsAffineOpen U)
  (e : OpenPartialHomeomorph
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (RegularSmoothness.NativeModel X))

def affineOpenSchemeChart := ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) e

theorem affineOpenSchemeChart_mem
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
      (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)) :
    affineOpenSchemeChart X U hU e ∈ atlas (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  ⟨U, hU, e, he, rfl⟩

omit [Smooth X.hom] in
theorem affineOpenChartPreimage_le (V : Opens (RegularSmoothness.NativeModel X)) :
    Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen (affineOpenSchemeChart X U hU e) V ≤ Open.AffineIsoEvaluation.analyticOpen X U := by
  intro p hp
  obtain ⟨x, _, rfl⟩ := hp.1
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU x ∈ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (U : Set X.left)
  rw [← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap X U hU]
  exact Set.mem_range_self x

omit [Smooth X.hom] in
theorem affineOpenChart_return (V : Opens (RegularSmoothness.NativeModel X)) (hV : V ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) :
    OpenChartFormNaturality.affineOpenChartToOpen X U hU e ∘ Opens.inclusion hV ∘
        Holomorphic.ChartMaps.chartForward (affineOpenSchemeChart X U hU e) V =
      Opens.inclusion (affineOpenChartPreimage_le X U hU e V) := by
  funext x
  apply Subtype.ext
  rw [Function.comp_apply, Function.comp_apply, OpenChartFormNaturality.affineOpenChartToOpen, OpenSectionEvaluation.affineOpenPointInOpen_val]
  exact (affineOpenSchemeChart X U hU e).left_inv x.property.1

theorem affineOpenChart_pullback_restrict
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
      (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom))
    (V : Opens (RegularSmoothness.NativeModel X)) (hV : V ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e)
    (n : ℕ) (a : Holomorphic.DeRhamComplex.forms (RegularSmoothness.NativeModel X) (Open.AffineIsoEvaluation.analyticOpen X U) n) :
    Holomorphic.HolomorphicPullback.pullback (Holomorphic.ChartMaps.chartForward (affineOpenSchemeChart X U hU e) V)
        (Holomorphic.ChartMaps.chartForward_holomorphic _ (affineOpenSchemeChart_mem X U hU e he) V) n
      (Holomorphic.HolomorphicPullback.pullback (Opens.inclusion hV) (contMDiff_inclusion (I := 𝓘(ℂ, RegularSmoothness.NativeModel X)) hV) n
        (Holomorphic.HolomorphicPullback.pullback (OpenChartFormNaturality.affineOpenChartToOpen X U hU e)
          (OpenChartFormNaturality.affineOpenChartToOpen_holomorphic X U hU e he) n a)) =
      Holomorphic.HolomorphicPullback.pullback (Opens.inclusion (affineOpenChartPreimage_le X U hU e V))
        (contMDiff_inclusion (I := 𝓘(ℂ, RegularSmoothness.NativeModel X)) (affineOpenChartPreimage_le X U hU e V)) n a := by
  rw [← Holomorphic.HolomorphicPullback.pullback_comp, ← Holomorphic.HolomorphicPullback.pullback_comp]
  have hi := affineOpenChart_return X U hU e V hV
  change Holomorphic.HolomorphicPullback.pullback (OpenChartFormNaturality.affineOpenChartToOpen X U hU e ∘ Opens.inclusion hV ∘
    Holomorphic.ChartMaps.chartForward (affineOpenSchemeChart X U hU e) V) _ n a = _
  simp only [hi]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenChartRestriction
