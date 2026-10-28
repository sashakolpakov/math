import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation
import OAI.AlgebraicTopology.DeRham.Comparison.Projective

/-! # Rational Integration Defect -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalIntegrationDefect.CM.Construction

noncomputable section

/-! A rational de Rham class gives an actual rational singular cocycle.
Its smooth restriction differs from integration by the coboundary of an
actual smooth singular zero-cochain. -/

open _root_.CategoryTheory

def rationalSmoothCocycle (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace V.toOver) n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles V.smoothSingularComplex n :=
  AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap V.bettiRestrictionCochain n
    (PositiveCohomologyConjugation.CM.Construction.complexCocycleOfRational (Betti.Scheme.schemePointSpace V.toOver) n c)

theorem rationalSmoothCocycle_class (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace V.toOver) n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass V.smoothSingularComplex n (rationalSmoothCocycle V n c) =
      V.rationalToSmoothSingular n
        (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace V.toOver) n c) := by
  rw [rationalSmoothCocycle, ← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  change V.bettiToSmoothSingular n
      (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℂ ℂ) (Betti.Scheme.schemePointSpace V.toOver) n
        (PositiveCohomologyConjugation.CM.Construction.complexCocycleOfRational (Betti.Scheme.schemePointSpace V.toOver) n c)) =
    V.bettiToSmoothSingular n
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace V.toOver) n
        (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace V.toOver) n c))
  rw [PositiveCohomologyConjugation.CM.Construction.rationalToComplexCohomology_class]

theorem rational_integration_defect (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : V.rationalCohomology 1)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (hform : (V.deRhamBettiIso 1).hom (V.deRhamClass 1 form) =
      V.rationalCohomologyInclusion 1 a) :
    ∃ (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace V.toOver) 1),
      AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace V.toOver) 1 c = a ∧
      ∃ b : V.smoothSingularComplex.X 0,
        V.smoothSingularComplex.d 0 1 b =
          (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle
            V.analyticModel V.analyticSpace 1 form).val -
          (rationalSmoothCocycle V 1 c).val := by
  obtain ⟨c, hc⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ)
    (Betti.Scheme.schemePointSpace V.toOver) 1 a
  refine ⟨c, hc, ?_⟩
  apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ V.smoothSingularComplex 0 _ _).mp
  rw [rationalSmoothCocycle_class, hc]
  have h := V.deRhamBettiIso_formClass 1 form
  rw [hform] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalIntegrationDefect.CM.Construction
