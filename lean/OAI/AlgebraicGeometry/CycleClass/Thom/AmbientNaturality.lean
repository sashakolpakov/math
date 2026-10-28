import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TransportRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TransportDifferentiable
import OAI.AlgebraicGeometry.CycleClass.Thom.Degree

/-! # Ambient Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.AmbientNaturality.Constructions

noncomputable section

/-! The genuine global Thom class is natural under holomorphic ambient
homeomorphisms, with the two actual immersion codimensions displayed. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.AmbientTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TransportRestriction.Constructions
  NormalPair.TransportDifferentiable.Constructions Degree.Constructions.ThomClass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E G H M N N' : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N]
  [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold 𝓘(ℂ, H) ω N'] [MetrizableSpace N']

theorem complexThomClassInDegree_ambientTransport
    (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω f)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) f x))
    (hc : Topology.IsClosedEmbedding f)
    (e : N ≃ₜ N') (he : MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, H) e)
    (hei : MDifferentiable 𝓘(ℂ, H) 𝓘(ℂ, G) e.symm)
    (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, H) ω (e ∘ f))
    (hgi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, H) (e ∘ f) x))
    (hgc : Topology.IsClosedEmbedding (e ∘ f))
    (p : ℕ) (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G = p)
    (hpg : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E H = p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPair.TransportRestriction.Constructions.ambientTransportMap e)
      (NormalPair.TransportRestriction.Constructions.ambientTransportMapsTo f e) (2 * p)
      (Degree.Constructions.ThomClass.complexThomClassInDegree (e ∘ f) hg hgi hgc p hpg) =
        Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi hc p hp := by
  subst hp
  apply Degree.Constructions.ThomClass.complexThomClassInDegree_unique f hf hi hc _ rfl
    (fun x => Geometric.ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi hc x)
    (fun x => Geometric.ComplexThom.Cycles.complexImmersionNormalPair_mdifferentiable f hf hi hc x)
  intro x
  apply NormalPair.TransportRestriction.Constructions.ambientTransport_normalizedRestriction f e (Geometric.ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi hc x)
  exact Degree.Constructions.ThomClass.complexThomClassInDegree_restrict (e ∘ f) hg hgi hgc _ hpg x
    (NormalPair.AmbientTransport.Constructions.transportNormalPair (Geometric.ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi hc x) e)
    (NormalPair.TransportDifferentiable.Constructions.transportNormalPair_mdifferentiable (Geometric.ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi hc x) e
      (Geometric.ComplexThom.Cycles.complexImmersionNormalPair_mdifferentiable f hf hi hc x) he hei)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.AmbientNaturality.Constructions
