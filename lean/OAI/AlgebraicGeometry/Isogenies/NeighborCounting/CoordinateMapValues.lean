import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTypedSubspaces

/-! # Coordinate Map Values -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateMapValues

/-! Giving an additive point equivalence its unique ZMod-linear
structure leaves the actual point values unchanged. -/

theorem zmodLinearEquiv_apply (q : ℕ) [Fact q.Prime] {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod q) V] [Module (ZMod q) W] (e : V ≃+ W) (x : V) :
    ActiveTypedSubspaces.zmodLinearEquiv q e x = e x := rfl

theorem coordinate_membership_trans {F V W : Type*} [Semiring F]
    [AddCommMonoid V] [AddCommMonoid W] [Module F V] [Module F W]
    (e : V ≃ₗ[F] W) (J : Submodule F W) (z : V) {P Q : Prop}
    (hP : e z ∈ J ↔ P) (hQ : e.toAddEquiv z ∈ J ↔ Q) : P ↔ Q :=
  hP.symm.trans hQ

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateMapValues
