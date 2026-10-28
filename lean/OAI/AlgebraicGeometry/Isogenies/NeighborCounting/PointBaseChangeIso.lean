import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.PointBaseChange

/-! # Point Base Change Iso -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointBaseChangeIso

noncomputable section

/-! The actual point comparison is compatible with a source group
isomorphism and its canonical pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.PointBaseChange

universe u

theorem baseChangedPointEquiv_sourceIso {S₁ S₂ S₀ : Scheme.{u}} (f : S₀ ⟶ S₁) (g : S₀ ⟶ S₂)
    (G₀ G₁ : Grp (Over S₁)) (H : Grp (Over S₂)) (i : G₀ ≅ G₁)
    (e : (Over.pullback f).mapGrp.obj G₁ ≅ (Over.pullback g).mapGrp.obj H)
    (a : Over.mk f ⟶ G₀.X) :
    GroupPointBaseChange.baseChangedPointEquiv f g G₀ H ((Over.pullback f).mapGrp.mapIso i ≪≫ e) a =
      GroupPointBaseChange.baseChangedPointEquiv f g G₁ H e (a ≫ i.hom.hom.hom) := by
  apply (GroupPointBaseChange.pointPullbackGroupEquiv g H).injective
  rw [Kernel.PointBaseChange.baseChangedPointEquiv_pullback, Kernel.PointBaseChange.baseChangedPointEquiv_pullback, Kernel.PointBaseChange.pointPullbackGroupEquiv_comp]
  exact (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointBaseChangeIso
