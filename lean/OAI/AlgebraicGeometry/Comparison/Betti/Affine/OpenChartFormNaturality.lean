import OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenSectionEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.SchemeChartFormNaturality

/-! # Open Chart Form Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenChartFormNaturality

noncomputable section

/-! The original realization on an affine open has the exact native chart formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  (U : X.left.Opens) (hU : IsAffineOpen U)
  (e : OpenPartialHomeomorph
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (RegularSmoothness.NativeModel X))
  (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
    (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom))

def affineOpenChartToOpen : Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e → Open.AffineIsoEvaluation.analyticOpen X U :=
  fun x => OpenSectionEvaluation.affineOpenPointInOpen X U hU (e.symm x)

include he in
theorem affineOpenChartToOpen_holomorphic :
    ContMDiff 𝓘(ℂ, RegularSmoothness.NativeModel X) 𝓘(ℂ, RegularSmoothness.NativeModel X) ∞ (affineOpenChartToOpen X U hU e) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  have hc : ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) e ∈
        atlas (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := ⟨U, hU, e, he, rfl⟩
  convert SchemeChartFormNaturality.affineChartToScheme_holomorphic X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) e hc using 1
  funext x
  exact OpenSectionEvaluation.affineOpenPointInOpen_val X U hU (e.symm x)

theorem openHolomorphicCochainMap_in_affineChart (n : ℕ) (a : Algebraic.Forms.Form Γ(X.left, U) n) :
    ChartFormEvaluation.affineChartHolomorphicFormMap e he n a =
      Holomorphic.HolomorphicPullback.pullback (affineOpenChartToOpen X U hU e) (affineOpenChartToOpen_holomorphic X U hU e he) n
        ((Algebraic.Holomorphic.openHolomorphicCochainMap X U).f n a) := by
  have h := Holomorphic.FormNaturality.Smooth.holomorphicFormMap_naturality
    (ChartFormEvaluation.affineChartContinuousEvaluation e he) (ChartFormEvaluation.affineChartEvaluation_realSmooth e he)
    (ChartFormEvaluation.affineChartEvaluation_complexSmooth e he) (Open.AffineIsoEvaluation.sectionEvaluationOn X U)
    (Open.SmoothEvaluation.sectionEvaluationOn_smooth X U) (HodgeConjecture.CMExtraction.HolomorphicSections.Kaehler.sectionEvaluationOn_holomorphic X U)
    (AlgHom.id ℂ Γ(X.left, U)) (affineOpenChartToOpen X U hU e)
    (affineOpenChartToOpen_holomorphic X U hU e he)
    (fun s x => (OpenSectionEvaluation.sectionEvaluationOn_affineOpen X U hU (e.symm x) s).symm) n a
  have hid : Algebraic.Forms.pullback (AlgHom.id ℂ Γ(X.left, U)) n a = a :=
    congrArg (fun k : Algebraic.Forms.Form Γ(X.left, U) n →ₗ[ℂ] Algebraic.Forms.Form Γ(X.left, U) n => k a)
      (Algebraic.Forms.pullback_id (A := Γ(X.left, U)) n)
  exact (congrArg (ChartFormEvaluation.affineChartHolomorphicFormMap e he n) hid.symm).trans h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.OpenChartFormNaturality
