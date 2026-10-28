import OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalPairRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalPairAnalytic
import OAI.AlgebraicGeometry.CycleClass.Thom.Degree
import Mathlib.Topology.Metrizable.Basic

/-! # Open Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.OpenNaturality.Constructions

noncomputable section

/-! The genuine Thom class restricts to the genuine Thom class in an
ambient open subset, using its native induced complex manifold structure. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions.PairTransport OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalPairRestriction.Constructions
  Open.NormalPairAnalytic.Constructions.Differentiable Degree.Constructions.ThomClass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E F M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ω N] [MetrizableSpace N]

local instance (U : Opens N) : MetrizableSpace U :=
  U.isOpenEmbedding'.isEmbedding.metrizableSpace

theorem complexThomClassInDegree_openAmbient
    (U : Opens N) (f : M → U)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))
    (hc : Topology.IsClosedEmbedding f)
    (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω (Subtype.val ∘ f))
    (hgi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) (Subtype.val ∘ f) x))
    (hgc : Topology.IsClosedEmbedding (Subtype.val ∘ f))
    (p : ℕ) (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E F = p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Open.NormalPairRestriction.Constructions.openAmbientTransportMap Subtype.val U.isOpenEmbedding')
      (Open.NormalPairRestriction.Constructions.openAmbientTransportMapsTo f Subtype.val U.isOpenEmbedding') (2 * p)
      (Degree.Constructions.ThomClass.complexThomClassInDegree (Subtype.val ∘ f) hg hgi hgc p hp) =
        Degree.Constructions.ThomClass.complexThomClassInDegree f hf hi hc p hp := by
  subst hp
  apply Degree.Constructions.ThomClass.complexThomClassInDegree_unique f hf hi hc _ rfl
    (fun x => Geometric.ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi hc x)
    (fun x => Geometric.ComplexThom.Cycles.complexImmersionNormalPair_mdifferentiable f hf hi hc x)
  intro x
  apply Open.NormalPairRestriction.Constructions.openAmbientTransport_normalizedRestriction f Subtype.val U.isOpenEmbedding'
    (Geometric.ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi hc x)
  exact Degree.Constructions.ThomClass.complexThomClassInDegree_restrict (Subtype.val ∘ f) hg hgi hgc _ rfl x
    (Open.NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair (Geometric.ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi hc x) Subtype.val U.isOpenEmbedding')
    (Open.NormalPairAnalytic.Constructions.Differentiable.openTransportNormalPair_mdifferentiable U (Geometric.ComplexNormalAtlas.Cycles.complexImmersionNormalPair f hf hi hc x)
      (Geometric.ComplexThom.Cycles.complexImmersionNormalPair_mdifferentiable f hf hi hc x))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.OpenNaturality.Constructions
