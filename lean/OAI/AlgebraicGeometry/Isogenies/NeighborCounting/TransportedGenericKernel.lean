import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.PointBaseChange

/-! # Transported Generic Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedGenericKernel

noncomputable section

/-! Put an integral kernel into the original generic source through
the actual base-change group isomorphism. Its finite flat model and
pointwise membership are both constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.PointBaseChange
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

universe u

variable {S₁ S₂ S₀ : Scheme.{u}} (f : S₀ ⟶ S₁) (g : S₀ ⟶ S₂)
  (G : Grp (Over S₁)) (H : Grp (Over S₂))
  (e : (Over.pullback f).mapGrp.obj G ≅ (Over.pullback g).mapGrp.obj H)
  (K : Kernel.Properties.FiniteFlatKernel H.X)

def transportedGenericKernel : Kernel.Properties.FiniteFlatKernel ((Over.pullback f).obj G.X) := by
  let eraw : (Over.pullback g).obj H.X ≅ (Over.pullback f).obj G.X :=
    (Grp.forget _).mapIso e.symm
  have : IsMonHom eraw.hom := e.inv.hom.isMonHom_hom
  exact (K.pullback g).mapIso eraw

theorem transportedGenericKernel_membership (a : Over.mk f ⟶ G.X) :
    (∃ b : Over.mk (𝟙 S₀) ⟶ (transportedGenericKernel f g G H e K).carrier,
      b ≫ (transportedGenericKernel f g G H e K).inclusion = GroupPointBaseChange.pointPullbackGroupEquiv f G a) ↔
    ∃ b : Over.mk g ⟶ K.carrier, b ≫ K.inclusion = GroupPointBaseChange.baseChangedPointEquiv f g G H e a := by
  let eraw : (Over.pullback g).obj H.X ≅ (Over.pullback f).obj G.X :=
    (Grp.forget _).mapIso e.symm
  have : IsMonHom eraw.hom := e.inv.hom.isMonHom_hom
  have hm := Kernel.PointBaseChange.mapIsoKernel_membership (K.pullback g) eraw (GroupPointBaseChange.pointPullbackGroupEquiv f G a)
  have hp := Kernel.PointBaseChange.baseChangedPointEquiv_pullback f g G H e a
  have he := congrArg
    (fun z : Over.mk (𝟙 S₀) ⟶ ((Over.pullback g).mapGrp.obj H).X =>
      ∃ b : Over.mk (𝟙 S₀) ⟶ (K.pullback g).carrier, b ≫ (K.pullback g).inclusion = z) hp
  exact hm.trans (he.symm.to_iff.trans
    (Kernel.PointBaseChange.pullbackKernel_membership K g (GroupPointBaseChange.baseChangedPointEquiv f g G H e a)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedGenericKernel
