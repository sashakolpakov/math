import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionRoundTrip
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCoordinates

/-! # Projector Subspace Membership -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorSubspaceMembership

noncomputable section

/-! Equal native projectors preserve the ambient inclusion and the
membership predicate on dimension-indexed killed-point subspaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionRoundTrip OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCoordinates
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTypedSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveLevel

theorem killedPointSubspaceEquiv_membership (q : ℕ) [Fact q.Prime]
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) (n : ℕ)
    (V : {V : Submodule (ZMod q) (ActiveTorsionChoices.killedSubgroup q G) // Module.finrank (ZMod q) V = n})
    (x : ActiveTorsionChoices.killedSubgroup q H) :
    x ∈ (SubspaceCoordinates.killedPointSubspaceEquiv q e n V).val ↔
      (Intrinsic.ActiveLevel.killedSubgroupEquiv q e).symm x ∈ V.val :=
  SubspaceCoordinates.dimensionSubspaceEquiv_membership (ActiveTypedSubspaces.zmodLinearEquiv q (Intrinsic.ActiveLevel.killedSubgroupEquiv q e)) n V x

theorem nativeBlockPointEquivOfEq_symm_inclusion {S : Scheme} {A T : Over S}
    [GrpObj A] [IsCommMonObj A] (n : ℕ) {p r : A ⟶ A} [IsMonHom p] [IsMonHom r]
    (h : p = r) (a : Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n r)) :
    ((ActionRoundTrip.nativeBlockPointEquivOfEq n h).symm a).toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p =
      a.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n r := by
  subst r
  rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorSubspaceMembership
