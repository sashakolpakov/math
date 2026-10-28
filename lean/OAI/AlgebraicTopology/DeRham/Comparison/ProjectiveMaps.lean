import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveIntegration
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
import OAI.Analysis.DifferentialForms.Manifold.ClosedPullback

/-! # Projective Maps -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveMaps.IntegralProjectiveVariety

noncomputable section

/-!
# Actual pullbacks between projective varieties

Every map in this file comes from a morphism over the specified complex
base. Its analytic smoothness follows from the proved native regular atlas;
no continuity or differentiability assumption is added to the morphism.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

variable {V W T : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}

/-- An algebraic morphism is complex analytic on the actual point manifolds. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complex_contMDiff_map (φ : V.toOver ⟶ W.toOver) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, V.analyticModel)) (𝓘(ℂ, W.analyticModel)) r
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) := by
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  let : IsIntegral W.toOver.left := W.property
  let : Smooth W.toOver.hom := W.presentation.smooth
  exact AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map φ r

/-- The same algebraic morphism is smooth on the underlying real manifolds. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map (φ : V.toOver ⟶ W.toOver) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℝ, V.analyticModel)) (𝓘(ℝ, W.analyticModel)) r
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) := by
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  let : IsIntegral W.toOver.left := W.property
  let : Smooth W.toOver.hom := W.presentation.smooth
  exact AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map φ r

/-- Pullback of the genuine de Rham complex along an algebraic morphism. -/
abbrev _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamCochainPullback (φ : V.toOver ⟶ W.toOver) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex W.analyticModel W.analyticSpace ⟶
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex V.analyticModel V.analyticSpace :=
  Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map φ ∞)

/-- Pullback on genuine de Rham cohomology. -/
abbrev _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback (φ : V.toOver ⟶ W.toOver) (n : ℕ) :
    W.deRhamCohomology n ⟶ V.deRhamCohomology n :=
  HomologicalComplex.homologyMap (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamCochainPullback φ) n

/-- Pullback of actual complex singular cohomology. -/
abbrev _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback (φ : V.toOver ⟶ W.toOver) (n : ℕ) :
    W.complexCohomology n ⟶ V.complexCohomology n :=
  AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n φ

/-- Pullback of actual rational singular cohomology. -/
abbrev _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback (φ : V.toOver ⟶ W.toOver) (n : ℕ) :
    W.rationalCohomology n ⟶ V.rationalCohomology n :=
  AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n φ

/-- Algebraic pullback commutes with the actual inclusion of rational
singular coefficients into complex singular coefficients. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCohomologyInclusion_pullback (φ : V.toOver ⟶ W.toOver) (n : ℕ) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback φ n ≫ V.rationalCohomologyInclusion n =
      W.rationalCohomologyInclusion n ≫
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map
          (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback φ n) :=
  AlgebraicGeometry.Betti.Scheme.schemeBettiRationalInclusion_naturality φ n

end

end OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveMaps.IntegralProjectiveVariety
