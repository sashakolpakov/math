import OAI.Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop
import OAI.Geometry.ComplexTorus.RiemannProjectivity.FormTransportIff
import OAI.AlgebraicTopology.DeRham.Comparison.Projective

/-! # Intrinsic Pure Comparison -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.IntrinsicPureComparison.Constructions.IntegrationTransport

/-! # RiemannProjectivity: the native de Rham comparison commutes with period pullback -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem betti_pullback_deRham
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E), 𝓘(ℂ, V.analyticModel)⟯ V.analyticSpace)
    (n : ℕ) (a : V.deRhamCohomology n) :
    (BettiTransportTop.Constructions.BettiTransport.iso ℂ e.toHomeomorph n).hom ((V.deRhamBettiIso n).hom a) =
      BettiDe.Constructions.Betti.deRhamBettiEquiv Φ n
        ((Analysis.DifferentialForms.Manifold.DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph (FormTransportIff.Constructions.FormTransport.realDiffeomorph e) n).hom a) := by
  let r := FormTransportIff.Constructions.FormTransport.realDiffeomorph e
  let : QuasiIso (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus) :=
    AlgebraicTopology.DeRham.Comparison.Manifold.smoothSimplexIntegrationCochainMap_quasiIso_compact (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus
  let : QuasiIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (ModuleCat.of ℂ ℂ) Φ.periodTorus) :=
    AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison.quasiIso_manifoldSmoothCochainRestriction (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus
  have h := AlgebraicGeometry.Betti.CohomologySpan.Realization.cohomologySpanIso_naturality
    V.deRhamIntegrationCochain V.bettiRestrictionCochain
    (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus)
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (ModuleCat.of ℂ ℂ) Φ.periodTorus)
    (Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback r r.contMDiff)
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) V.analyticModel (ModuleCat.of ℂ ℂ) r r.contMDiff)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) (BettiTransportTop.Constructions.BettiTransport.topIso e.toHomeomorph).hom)
    (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap_naturality r r.contMDiff).symm
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality (ModuleCat.of ℂ ℂ) r r.contMDiff).symm n
  exact ConcreteCategory.congr_hom h a

theorem betti_pullback_formClass
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E), 𝓘(ℂ, V.analyticModel)⟯ V.analyticSpace)
    (n : ℕ) (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace n) :
    (BettiTransportTop.Constructions.BettiTransport.iso ℂ e.toHomeomorph n).hom ((V.deRhamBettiIso n).hom (V.deRhamClass n a)) =
      BettiDe.Constructions.Betti.deRhamBettiEquiv Φ n
        (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus n (FormTransportIff.Constructions.FormTransport.closedForms e n a)) := by
  rw [betti_pullback_deRham]
  rw [Analysis.DifferentialForms.Manifold.DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph_class]
  rfl

end Geometry.ComplexTorus.RiemannProjectivity.IntrinsicPureComparison.Constructions.IntegrationTransport

namespace Geometry.ComplexTorus.RiemannProjectivity.IntrinsicPureComparison.Constructions

/-! # RiemannProjectivity: native Hodge type is precisely the period torus's closed-form type -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem pureBetti_iff
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E), 𝓘(ℂ, V.analyticModel)⟯ V.analyticSpace)
    (p q : ℕ) (c : V.complexCohomology (p + q)) :
    c ∈ V.pureBettiSubspace p q ↔
      ∃ a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus (p + q),
        Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus p q a.val ∧
        BettiDe.Constructions.Betti.deRhamBettiEquiv Φ (p + q) (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus (p + q) a) =
          (BettiTransportTop.Constructions.BettiTransport.iso ℂ e.toHomeomorph (p + q)).hom c := by
  rw [V.mem_pureBettiSubspace_iff]
  constructor
  · rintro ⟨a, ha, heq⟩
    refine ⟨FormTransportIff.Constructions.FormTransport.closedForms e (p + q) a, ?_, ?_⟩
    · exact FormTransportIff.Constructions.FormTransport.pure_pullback e p q a ((Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mpr ha)
    · rw [← IntegrationTransport.betti_pullback_formClass, heq]
  · rintro ⟨a, ha, heq⟩
    obtain ⟨b, rfl⟩ := (FormTransportIff.Constructions.FormTransport.closedForms e (p + q)).surjective a
    refine ⟨b, ?_, ?_⟩
    · exact (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mp ((FormTransportIff.Constructions.FormTransport.pure_iff e p q b).mp ha)
    · apply (BettiTransportTop.Constructions.BettiTransport.iso ℂ e.toHomeomorph (p + q)).toLinearEquiv.injective
      exact (IntegrationTransport.betti_pullback_formClass Φ V e (p + q) b).trans heq

end Geometry.ComplexTorus.RiemannProjectivity.IntrinsicPureComparison.Constructions

end

end OAI
