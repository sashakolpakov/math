import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicBetti
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.TorusRealManifold
import OAI.Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop
import OAI.Geometry.ComplexTorus.RiemannProjectivity.FormTransportIff
import OAI.AlgebraicTopology.DeRham.Comparison.Projective

/-! # Algebraic Integration Transport -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicIntegrationTransport.CM.Abelian.Algebraization.IntegrationTransport

/-! # CMAbelianVariety: the native de Rham comparison commutes with period pullback -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

variable (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData) (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem betti_pullback_deRham
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, V.analyticModel)⟯ V.analyticSpace)
    (n : ℕ) (a : V.deRhamCohomology n) :
    (Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop.Constructions.BettiTransport.iso ℂ e.toHomeomorph n).hom ((V.deRhamBettiIso n).hom a) =
      AlgebraicBetti.CM.Abelian.Algebraization.Betti.deRhamBettiEquiv Φ n
        ((Analysis.DifferentialForms.Manifold.DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph (Geometry.ComplexTorus.RiemannProjectivity.FormTransportIff.Constructions.FormTransport.realDiffeomorph e) n).hom a) := by
  let r := Geometry.ComplexTorus.RiemannProjectivity.FormTransportIff.Constructions.FormTransport.realDiffeomorph e
  let : QuasiIso (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap (Φ.space) Φ.periodTorus) :=
    AlgebraicTopology.DeRham.Comparison.Manifold.smoothSimplexIntegrationCochainMap_quasiIso_compact (Φ.space) Φ.periodTorus
  let : QuasiIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction (Φ.space) (ModuleCat.of ℂ ℂ) Φ.periodTorus) :=
    AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison.quasiIso_manifoldSmoothCochainRestriction (Φ.space) Φ.periodTorus
  have h := Betti.CohomologySpan.Realization.cohomologySpanIso_naturality
    V.deRhamIntegrationCochain V.bettiRestrictionCochain
    (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap (Φ.space) Φ.periodTorus)
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction (Φ.space) (ModuleCat.of ℂ ℂ) Φ.periodTorus)
    (Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback r r.contMDiff)
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback (Φ.space) V.analyticModel (ModuleCat.of ℂ ℂ) r r.contMDiff)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) (Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop.Constructions.BettiTransport.topIso e.toHomeomorph).hom)
    (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap_naturality r r.contMDiff).symm
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality (ModuleCat.of ℂ ℂ) r r.contMDiff).symm n
  exact ConcreteCategory.congr_hom h a

theorem betti_pullback_formClass
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, V.analyticModel)⟯ V.analyticSpace)
    (n : ℕ) (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace n) :
    (Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop.Constructions.BettiTransport.iso ℂ e.toHomeomorph n).hom ((V.deRhamBettiIso n).hom (V.deRhamClass n a)) =
      AlgebraicBetti.CM.Abelian.Algebraization.Betti.deRhamBettiEquiv Φ n
        (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (Φ.space) Φ.periodTorus n (Geometry.ComplexTorus.RiemannProjectivity.FormTransportIff.Constructions.FormTransport.closedForms e n a)) := by
  rw [betti_pullback_deRham]
  rw [Analysis.DifferentialForms.Manifold.DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph_class]
  rfl

end AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicIntegrationTransport.CM.Abelian.Algebraization.IntegrationTransport

namespace AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicIntegrationTransport.CM.Abelian.Algebraization.IntrinsicPureComparison

/-! # CMAbelianVariety: native Hodge type is precisely the period torus's closed-form type -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

variable (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData) (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem pureBetti_iff
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, V.analyticModel)⟯ V.analyticSpace)
    (p q : ℕ) (c : V.complexCohomology (p + q)) :
    c ∈ V.pureBettiSubspace p q ↔
      ∃ a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (Φ.space) Φ.periodTorus (p + q),
        Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Φ.space) Φ.periodTorus p q a.val ∧
        AlgebraicBetti.CM.Abelian.Algebraization.Betti.deRhamBettiEquiv Φ (p + q) (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (Φ.space) Φ.periodTorus (p + q) a) =
          (Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop.Constructions.BettiTransport.iso ℂ e.toHomeomorph (p + q)).hom c := by
  rw [V.mem_pureBettiSubspace_iff]
  constructor
  · rintro ⟨a, ha, heq⟩
    refine ⟨Geometry.ComplexTorus.RiemannProjectivity.FormTransportIff.Constructions.FormTransport.closedForms e (p + q) a, ?_, ?_⟩
    · exact Geometry.ComplexTorus.RiemannProjectivity.FormTransportIff.Constructions.FormTransport.pure_pullback e p q a ((Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mpr ha)
    · rw [← IntegrationTransport.betti_pullback_formClass, heq]
  · rintro ⟨a, ha, heq⟩
    obtain ⟨b, rfl⟩ := (Geometry.ComplexTorus.RiemannProjectivity.FormTransportIff.Constructions.FormTransport.closedForms e (p + q)).surjective a
    refine ⟨b, ?_, ?_⟩
    · exact (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mp ((Geometry.ComplexTorus.RiemannProjectivity.FormTransportIff.Constructions.FormTransport.pure_iff e p q b).mp ha)
    · apply (Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop.Constructions.BettiTransport.iso ℂ e.toHomeomorph (p + q)).toLinearEquiv.injective
      exact (IntegrationTransport.betti_pullback_formClass Φ V e (p + q) b).trans heq

end AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicIntegrationTransport.CM.Abelian.Algebraization.IntrinsicPureComparison

end

end OAI
