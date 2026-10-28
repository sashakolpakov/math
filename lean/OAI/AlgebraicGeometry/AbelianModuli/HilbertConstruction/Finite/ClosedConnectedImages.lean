import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Closed Connected Images -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ClosedConnectedImages

/-! A finite closed continuous image of a connected space in a Jacobson space is a singleton. -/

universe u v

theorem finite_closed_connected_range_subsingleton
    {X : Type u} [TopologicalSpace X] [ConnectedSpace X]
    {Y : Type v} [TopologicalSpace Y] [JacobsonSpace Y]
    (f : X → Y) (hf : Continuous f) (hc : IsClosed (Set.range f)) (hfinite : (Set.range f).Finite) :
    (Set.range f).Subsingleton := by
  have : Finite (Set.range f) := hfinite.to_subtype
  have : JacobsonSpace (Set.range f) := JacobsonSpace.of_isClosedEmbedding hc.isClosedEmbedding_subtypeVal
  have : ConnectedSpace (Set.range f) := Set.rangeFactorization_surjective.connectedSpace hf.rangeFactorization
  have : Subsingleton (Set.range f) := subsingleton_of_preconnected_totallyDisconnected
  exact fun x hx y hy => congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : Set.range f) ⟨y, hy⟩)

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ClosedConnectedImages
