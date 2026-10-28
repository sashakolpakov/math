import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.ChangeSource
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalPairAnalytic

/-! # Restriction Normal Pair -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionNormalPair.Constructions

noncomputable section

/-! A normal pair for the actual open restriction also gives a
normal pair for the original full immersion, on the same ambient image. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.ChangeSource.Constructions
  NormalNeighborhoodInverse.Constructions.PairTransport NormalPairAnalytic.Constructions.Differentiable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p) (U : Opens V.analyticSpace)

theorem restriction_mapsTo : Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion V.analyticSpace (U : Set V.analyticSpace))
    (Set.range (Closed.ImmersionOpenRestriction.Constructions.restrict Z U).regularComplementInclusion)ᶜ (Set.range Z.regularComplementInclusion)ᶜ := by
  intro y hy h
  obtain ⟨z, hz⟩ := h
  apply hy
  have hzU : Z.regularComplementInclusion z ∈ U := hz.symm ▸ y.property
  exact ⟨⟨z, hzU⟩, Subtype.ext hz⟩

variable (x : Closed.ImmersionOpenRestriction.Constructions.sourceOpen Z U)
  (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ)
    (Closed.ImmersionOpenRestriction.Constructions.restrict Z U).regularComplementInclusion x)

theorem lifted_image_iff (y : V.analyticSpace)
    (hy : y ∈ (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair Q Subtype.val U.isOpenEmbedding').neighborhood) :
    y ∈ Set.range Z.regularComplementInclusion ↔
      y ∈ Set.range (Subtype.val ∘ (Closed.ImmersionOpenRestriction.Constructions.restrict Z U).regularComplementInclusion) := by
  rw [NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair_neighborhood] at hy
  obtain ⟨w, _, rfl⟩ := hy
  constructor
  · rintro ⟨z, hz⟩
    have hzU : Z.regularComplementInclusion z ∈ U := hz.symm ▸ w.property
    exact ⟨⟨z, hzU⟩, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z.val, hz⟩

def liftedNormalPair : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ)
    Z.regularComplementInclusion x.val :=
  NormalPair.ChangeSource.Constructions.changeSource (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalPair Q Subtype.val U.isOpenEmbedding')
    Z.regularComplementInclusion x.val rfl (lifted_image_iff Z U x Q)

theorem liftedNormalPair_mdifferentiable
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ))) :
    (liftedNormalPair Z U x Q).ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) :=
  NormalPairAnalytic.Constructions.Differentiable.openTransportNormalPair_mdifferentiable U Q hQ

theorem liftedNeighborhood_mapsTo :
    Set.MapsTo (NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalNeighborhoodMap Q Subtype.val U.isOpenEmbedding')
      Q.relativeComplement (liftedNormalPair Z U x Q).relativeComplement := by
  intro y hy
  exact restriction_mapsTo Z U hy

theorem liftedNeighborhood_normalCoordinate :
    NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalNeighborhoodMap Q Subtype.val U.isOpenEmbedding' ≫
      (liftedNormalPair Z U x Q).normalCoordinate = Q.normalCoordinate :=
  NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalNeighborhoodMap_normalCoordinate Q Subtype.val U.isOpenEmbedding'

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionNormalPair.Constructions
