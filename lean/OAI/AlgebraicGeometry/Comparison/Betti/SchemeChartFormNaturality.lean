import OAI.AlgebraicGeometry.Comparison.Betti.Affine.SectionAlgebra
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartFormEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FormNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartMaps
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Holomorphic

/-! # Scheme Chart Form Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SchemeChartFormNaturality

noncomputable section

/-! The native affine-chart symbol map is the actual pullback of the original scheme realization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartMaps

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  (A : CommAlgCat.{0} ℂ) (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion f.left]
  (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (RegularSmoothness.NativeModel X))

def affineChartToScheme : Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X :=
  fun x => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f (e.symm x)

theorem affineChartToScheme_holomorphic
    (hC : ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A f e ∈ atlas (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) :
    ContMDiff 𝓘(ℂ, RegularSmoothness.NativeModel X) 𝓘(ℂ, RegularSmoothness.NativeModel X) ∞ (affineChartToScheme X A f e) :=
  Holomorphic.ChartMaps.chartInverse_holomorphic (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A f e) hC (Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) le_rfl

theorem globalHolomorphicCochainMap_in_affineChart
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom))
    (hC : ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A f e ∈ atlas (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (n : ℕ) (a : Algebraic.Forms.Form Γ(X.left, ⊤) n) :
    Affine.ChartFormEvaluation.affineChartHolomorphicFormMap e he n
        (Algebraic.Forms.pullback (Affine.SectionAlgebra.affineTestSectionPullback A f) n a) =
      Holomorphic.HolomorphicPullback.pullback (affineChartToScheme X A f e) (affineChartToScheme_holomorphic X A f e hC) n
        ((Algebraic.Holomorphic.globalHolomorphicCochainMap X).f n a) := by
  exact Holomorphic.FormNaturality.Smooth.holomorphicFormMap_naturality
    (Affine.ChartFormEvaluation.affineChartContinuousEvaluation e he) (Affine.ChartFormEvaluation.affineChartEvaluation_realSmooth e he)
    (Affine.ChartFormEvaluation.affineChartEvaluation_complexSmooth e he) (RegularFunctions.globalSectionContinuousAlgHom X)
    (fun s => RegularSmoothness.globalEvaluation_real_contMDiff X s ∞)
    (fun s => RegularSmoothness.globalEvaluation_contMDiff X s ∞) (Affine.SectionAlgebra.affineTestSectionPullback A f)
    (affineChartToScheme X A f e) (affineChartToScheme_holomorphic X A f e hC)
    (fun s x => Affine.SectionAlgebra.affineTestSectionPullback_evaluation A f (e.symm x) s) n a

end

end OAI.AlgebraicGeometry.Comparison.Betti.SchemeChartFormNaturality
