import OAI.AlgebraicGeometry.CycleClass.Thom.OpenImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.ChangeSource
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalPairAnalytic

/-! # Open Normal Pair -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.OpenNormalPair.Constructions.Raw

noncomputable section

/-! Normal pairs for open restrictions lift to the original actual immersion, with arbitrary complex model spaces. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.OpenImmersion.Constructions.Raw OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.ChangeSource.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions.PairTransport OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalPairAnalytic.Constructions.Differentiable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N E G : Type} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω f) (U : Opens N)
  {p : ℕ} (x : GraphOpenImmersion.Constructions.graphSourceOpen f hf U)
  (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) (GraphOpenImmersion.Constructions.restrictedBase f hf U) x)

theorem lifted_image_iff (y : N)
    (hy : y ∈ (Open.NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair Q Subtype.val U.isOpenEmbedding').neighborhood) :
    y ∈ Set.range f ↔ y ∈ Set.range (Subtype.val ∘ GraphOpenImmersion.Constructions.restrictedBase f hf U) := by
  rw [Open.NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair_neighborhood] at hy
  obtain ⟨w, _, rfl⟩ := hy
  constructor
  · rintro ⟨z, hz⟩
    have hzU : f z ∈ U := hz.symm ▸ w.property
    exact ⟨⟨z, hzU⟩, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z.val, hz⟩

def liftedNormalPair : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x.val :=
  NormalPair.ChangeSource.Constructions.changeSource (Open.NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair Q Subtype.val U.isOpenEmbedding') f x.val rfl
    (lifted_image_iff f hf U x Q)

theorem liftedNormalPair_mdifferentiable
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ))) :
    (liftedNormalPair f hf U x Q).ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)) :=
  Open.NormalPairAnalytic.Constructions.Differentiable.openTransportNormalPair_mdifferentiable U Q hQ

theorem liftedNeighborhood_mapsTo : Set.MapsTo
    (Open.NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalNeighborhoodMap Q Subtype.val U.isOpenEmbedding') Q.relativeComplement
    (liftedNormalPair f hf U x Q).relativeComplement :=
  fun _ hy => OpenImmersion.Constructions.Raw.restriction_mapsTo f hf U hy

theorem liftedNeighborhood_normalCoordinate :
    Open.NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalNeighborhoodMap Q Subtype.val U.isOpenEmbedding' ≫
      (liftedNormalPair f hf U x Q).normalCoordinate = Q.normalCoordinate :=
  Open.NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalNeighborhoodMap_normalCoordinate Q Subtype.val U.isOpenEmbedding'

end

end OAI.AlgebraicGeometry.CycleClass.Thom.OpenNormalPair.Constructions.Raw
