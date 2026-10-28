import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveLevel
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Subspace Coordinates -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCoordinates

noncomputable section

/-! Transport dimension-indexed subspaces through actual point-group
coordinates. The subgroup membership formula and dimension are preserved. -/

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTypedSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveLevel

variable {F V W : Type*} [Field F] [AddCommGroup V] [AddCommGroup W]
  [Module F V] [Module F W]

def dimensionSubspaceEquiv (e : V ≃ₗ[F] W) (n : ℕ) :
    {L : Submodule F V // Module.finrank F L = n} ≃
      {L : Submodule F W // Module.finrank F L = n} :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (fun L => by
    change Module.finrank F L = n ↔ Module.finrank F (L.map e.toLinearMap) = n
    rw [e.finrank_map_eq])

theorem dimensionSubspaceEquiv_membership (e : V ≃ₗ[F] W) (n : ℕ)
    (L : {L : Submodule F V // Module.finrank F L = n}) (x : W) :
    x ∈ (dimensionSubspaceEquiv e n L).val ↔ e.symm x ∈ L.val :=
  Submodule.mem_map_equiv L.val

def killedPointSubspaceEquiv (q : ℕ) [Fact q.Prime]
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) (n : ℕ) :
    {L : Submodule (ZMod q) (ActiveTorsionChoices.killedSubgroup q G) // Module.finrank (ZMod q) L = n} ≃
      {L : Submodule (ZMod q) (ActiveTorsionChoices.killedSubgroup q H) // Module.finrank (ZMod q) L = n} :=
  dimensionSubspaceEquiv (ActiveTypedSubspaces.zmodLinearEquiv q (Intrinsic.ActiveLevel.killedSubgroupEquiv q e)) n

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCoordinates
