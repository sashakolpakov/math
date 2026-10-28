import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodTorusManifoldAgreement
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodMap
import OAI.Analysis.DifferentialForms.Manifold.DeRhamDiffeomorph
import OAI.Analysis.DifferentialForms.Manifold.Holomorphic
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicAbelianTorusModel

/-! # Abelian Period Map -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AbelianPeriodMap.CM.Construction

noncomputable section

/-! Algebraizing the actual projective period torus gives an abelian
target for the constructed period map, preserving its surjective H¹ pullback. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

open scoped OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientManifold.CM.Construction.ComplexLatticeQuotient
  QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient

variable {Index : Type} [Fintype Index] [DecidableEq Index] (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (b : Module.Basis Index ℚ (V.rationalCohomology 1))
  (H : WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1))
  (hH : H.holomorphic = (V.pureBettiSubspace 1 0).comap
    (CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1))
  (P : CM.Polarization.WeightOnePolarization H)

include b H hH P in
theorem exists_abelian_period_map_h1_surjective :
    ∃ (A : CMAbelianVariety.CM.AbelianVariety) (f : C(V.analyticSpace, A.variety.analyticSpace)),
      MDifferentiable 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, A.variety.analyticModel) f ∧
      ∃ hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, A.variety.analyticModel) ∞ f,
        Function.Surjective (Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback f hf 1) := by
  let D := PeriodTorusProjective.CM.Construction.rationalH1ProjectivePeriodData V b H hH P
  obtain ⟨A, ⟨e⟩⟩ := HodgeConjecture.CMVariety.AlgebraicAbelianTorusModel.CM.Algebraization.AbelianTorusModel.exists_abelian_model D
  let e' : PeriodLattice.CM.Construction.RationalH1PeriodTorus V b ≃ₘ⟮𝓘(ℂ, PeriodLattice.CM.Construction.RationalH1PeriodSpace V b),
      𝓘(ℂ, A.variety.analyticModel)⟯ A.variety.analyticSpace := e
  let eR : PeriodLattice.CM.Construction.RationalH1PeriodTorus V b ≃ₘ⟮𝓘(ℝ, PeriodLattice.CM.Construction.RationalH1PeriodSpace V b),
      𝓘(ℝ, A.variety.analyticModel)⟯ A.variety.analyticSpace :=
    { toEquiv := e'.toEquiv
      contMDiff_toFun := Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex e'.contMDiff
      contMDiff_invFun := Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex e'.symm.contMDiff }
  obtain ⟨p, hph, hp, hps⟩ := PeriodMap.CM.Construction.exists_holomorphic_period_map_h1_surjective V b
  let f : C(V.analyticSpace, A.variety.analyticSpace) := ⟨e' ∘ p, e'.continuous.comp p.continuous⟩
  have hfh : MDifferentiable 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, A.variety.analyticModel) f :=
    (e'.contMDiff.mdifferentiable (by simp)).comp hph
  have hfr : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, A.variety.analyticModel) ∞ f :=
    eR.contMDiff.comp hp
  refine ⟨A, f, hfh, hfr, ?_⟩
  intro c
  obtain ⟨z, hz⟩ := hps c
  obtain ⟨w, hw⟩ := (Analysis.DifferentialForms.Manifold.DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph eR 1).toLinearEquiv.surjective z
  change (Analysis.DifferentialForms.Manifold.DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph eR 1).hom w = z at hw
  refine ⟨w, ?_⟩
  change Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback (eR ∘ p) (eR.contMDiff.comp hp) 1 w = c
  rw [Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback_comp p hp eR eR.contMDiff 1, ModuleCat.comp_apply]
  change Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback p hp 1
    ((Analysis.DifferentialForms.Manifold.DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph eR 1).hom w) = c
  rw [hw, hz]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AbelianPeriodMap.CM.Construction
