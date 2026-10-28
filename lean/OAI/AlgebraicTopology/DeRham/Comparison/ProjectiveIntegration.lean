import OAI.AlgebraicGeometry.Betti.ProjectiveCohomology
import OAI.AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain

/-! # Projective Integration -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveIntegration.IntegralProjectiveVariety

noncomputable section

/-!
# The two genuine comparison maps on a projective variety

The point space and its smooth structure are the proved realization of the
algebraic variety. One map integrates actual differential forms over smooth
singular simplices. The other restricts ordinary singular cochains to those
same simplices. This file only assembles those actual maps; invertibility is
supplied by the separate global comparison theorems.
-/

open _root_.CategoryTheory

/-- Complex-valued cochains on genuine smooth singular simplices of the
derived manifold of complex points. -/
abbrev _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.smoothSingularComplex (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :=
  Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains V.analyticModel (ModuleCat.of ℂ ℂ) V.analyticSpace

/-- Their actual kernel/image cohomology. -/
abbrev _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.smoothSingularCohomology (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :=
  V.smoothSingularComplex.homology n

/-- Integration of actual smooth forms over genuine smooth singular simplices. -/
abbrev _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamIntegrationCochain (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex V.analyticModel V.analyticSpace ⟶ V.smoothSingularComplex :=
  SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap V.analyticModel V.analyticSpace

/-- Ordinary singular cochains restrict to the same genuine smooth simplices. -/
abbrev _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.bettiRestrictionCochain (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) (AlgebraicGeometry.Betti.Scheme.schemePointSpace V.toOver) ⟶
      V.smoothSingularComplex :=
  Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction V.analyticModel
    (ModuleCat.of ℂ ℂ) V.analyticSpace

/-- The map on cohomology induced by actual differential-form integration. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamToSmoothSingular (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    V.deRhamCohomology n ⟶ V.smoothSingularCohomology n :=
  HomologicalComplex.homologyMap V.deRhamIntegrationCochain n

/-- The map on cohomology induced by ordinary-to-smooth restriction. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.bettiToSmoothSingular (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    V.complexCohomology n ⟶ V.smoothSingularCohomology n :=
  HomologicalComplex.homologyMap V.bettiRestrictionCochain n

/-- Rational coefficient inclusion followed by actual smooth restriction. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalToSmoothSingular (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    V.rationalCohomology n ⟶
      (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj (V.smoothSingularCohomology n) :=
  V.rationalCohomologyInclusion n ≫
    (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map (V.bettiToSmoothSingular n)

/-- Taking a closed representative commutes with the genuine integration map. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamToSmoothSingular_cycles (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex V.analyticModel V.analyticSpace).homologyπ n ≫
      V.deRhamToSmoothSingular n =
    HomologicalComplex.cyclesMap V.deRhamIntegrationCochain n ≫
      V.smoothSingularComplex.homologyπ n :=
  HomologicalComplex.homologyπ_naturality V.deRhamIntegrationCochain n

/-- Taking a closed representative also commutes with ordinary restriction. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.bettiToSmoothSingular_cycles (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    (Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ)
      (AlgebraicGeometry.Betti.Scheme.schemePointSpace V.toOver)).homologyπ n ≫ V.bettiToSmoothSingular n =
    HomologicalComplex.cyclesMap V.bettiRestrictionCochain n ≫
      V.smoothSingularComplex.homologyπ n :=
  HomologicalComplex.homologyπ_naturality V.bettiRestrictionCochain n

end

end OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveIntegration.IntegralProjectiveVariety
