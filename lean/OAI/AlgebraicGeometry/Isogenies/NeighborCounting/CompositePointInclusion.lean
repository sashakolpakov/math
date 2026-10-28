import Mathlib.Algebra.Group.Equiv.Defs

/-! # Composite Point Inclusion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompositePointInclusion

/-! Compute the inclusion of a point transported through three actual
additive equivalences from the two component inclusion identities. -/

theorem inverse_composite_inclusion {X Y Z W V : Type*}
    [Add X] [Add Y] [Add Z] [Add W]
    (e : X ≃+ Y) (f : Y ≃+ Z) (g : W ≃+ Z)
    (ix : X → V) (iy : Y → V) (iw : W → V)
    (he : ∀ y, ix (e.symm y) = iy y)
    (hf : ∀ w, iy (f.symm (g w)) = iw w) (w : W) :
    ix ((e.trans (f.trans g.symm)).symm w) = iw w :=
  (he (f.symm (g w))).trans (hf w)

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompositePointInclusion
