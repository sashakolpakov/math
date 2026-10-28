import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AbelianPeriodMap
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveNaturality
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicAlgebraizationGraph

/-! # Algebraic Period Map -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AlgebraicPeriodMap.CM.Construction

noncomputable section

/-! The actual holomorphic period map algebraizes to a morphism into an
abelian variety, with its genuine de Rham H¹ pullback still surjective. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

theorem exists_algebraic_map_of_holomorphic (V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (f : C(V.analyticSpace, W.analyticSpace))
    (hf : MDifferentiable 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, W.analyticModel) f) :
    ∃ g : V.toOver ⟶ W.toOver, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g = f := by
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  let : IsProper V.toOver.hom := V.presentation.projective.isProper
  let : IsIntegral W.toOver.left := W.property
  let : Smooth W.toOver.hom := W.presentation.smooth
  let : IsProper W.toOver.hom := W.presentation.projective.isProper
  obtain ⟨g, hg⟩ := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicAlgebraizationGraph.Constructions.HolomorphicAlgebraization.exists_algebraic_map
    V.presentation.projective W.presentation.projective f hf
  exact ⟨g, funext hg⟩

theorem exists_algebraic_period_map_h1_surjective {Index : Type} [Fintype Index] [DecidableEq Index]
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (b : Module.Basis Index ℚ (V.rationalCohomology 1))
    (H : WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1))
    (hH : H.holomorphic = (V.pureBettiSubspace 1 0).comap
      (CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1))
    (P : CM.Polarization.WeightOnePolarization H) :
    ∃ (A : CMAbelianVariety.CM.AbelianVariety) (g : V.toOver ⟶ A.toOver),
      Function.Surjective (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback g 1) := by
  obtain ⟨A, f, hf, hfr, hs⟩ := AbelianPeriodMap.CM.Construction.exists_abelian_period_map_h1_surjective V b H hH P
  obtain ⟨g, hg⟩ := exists_algebraic_map_of_holomorphic V A.variety f hf
  refine ⟨A, g, ?_⟩
  change Function.Surjective
    (Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g)
      (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map g ∞) 1)
  simpa only [hg] using hs

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AlgebraicPeriodMap.CM.Construction
