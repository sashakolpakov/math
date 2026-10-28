import OAI.AlgebraicGeometry.CycleClass.Thom.SourceNormalRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.TangentNormalRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Degree

/-! # Source Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SourceNaturality.Constructions

noncomputable section

/-! The actual global Thom class is invariant under a surjective source
reparametrization and a norm-preserving complex identification of source models. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.SourceTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SourceNormalRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TangentCoordinates.Constructions
  TangentNormalRestriction.Constructions Degree.Constructions.ThomClass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E G H M M' N : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [TopologicalSpace M'] [ChartedSpace G M'] [IsManifold 𝓘(ℂ, G) ω M']
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold 𝓘(ℂ, H) ω N] [MetrizableSpace N]

theorem complexThomClassInDegree_sourceTransport
    (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, H) ω f)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, H) f x))
    (hc : Topology.IsClosedEmbedding f)
    (a : M' → M) (ha : Function.Surjective a)
    (e : E ≃L[ℂ] G) (he : ∀ v, ‖e v‖ = ‖v‖)
    (hg : ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, H) ω (f ∘ a))
    (hgi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, H) (f ∘ a) x))
    (hgc : Topology.IsClosedEmbedding (f ∘ a))
    (p : ℕ) (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E H = p)
    (hpg : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension G H = p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of N))
      (SourceNormalRestriction.Constructions.sourceAmbientMapsTo f a ha) (2 * p)
      (Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi hc p hp) =
        Degree.Constructions.ThomClass.complexThomClassInDegree (f ∘ a) hg hgi hgc p hpg := by
  subst hp
  apply Degree.Constructions.ThomClass.complexThomClassInDegree_unique (f ∘ a) hg hgi hgc _ hpg
    (fun x => NormalPair.TangentCoordinates.Constructions.tangentCoordinateNormalPair
      (NormalPair.SourceTransport.Constructions.sourceTransportNormalPair a ha x (Geometric.ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi hc (a x))) e he)
    (fun x => NormalPair.TangentCoordinates.Constructions.tangentCoordinateNormalPair_mdifferentiable _ e he
      (Geometric.ComplexThom.Cycles.complexImmersionNormalPair_mdifferentiable f hf hi hc (a x)))
  intro x
  apply TangentNormalRestriction.Constructions.tangentCoordinates_normalizedRestriction
  apply SourceNormalRestriction.Constructions.sourceTransport_normalizedRestriction
  exact Degree.Constructions.ThomClass.complexThomClassInDegree_restrict f hf hi hc _ rfl (a x)
    (Geometric.ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi hc (a x))
    (Geometric.ComplexThom.Cycles.complexImmersionNormalPair_mdifferentiable f hf hi hc (a x))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SourceNaturality.Constructions
