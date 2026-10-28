import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison

/-! # Iterated Action Family Iso -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IteratedActionFamilyIso.Family

noncomputable section

/-! Compare iterated PEL pullbacks through an actual isomorphism of
polarized action data, without expanding a concrete moduli family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family

variable {E : Type} [Field E] {S T U V : Scheme} {d N : ℕ} {δ : Fin d → ℕ}
  (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E d δ N S) (B : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E d δ N T)
  (f : U ⟶ S) (h : V ⟶ U) (g : V ⟶ T)
  (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso ((A.pullback f).pullback h) (B.pullback g))

def iteratedActionFamilyIso :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso (((ActionFamilyComparison.Family.actionFamily A).pullback f).pullback h) ((ActionFamilyComparison.Family.actionFamily B).pullback g) :=
  ((ActionFamilyComparison.Family.actionFamilyPullbackIso A f).pullback h).trans
    ((ActionFamilyComparison.Family.actionFamilyPullbackIso (A.pullback f) h).trans
      ((ActionFamilyComparison.Family.actionIsoToFamilyIso e).trans (ActionFamilyComparison.Family.actionFamilyPullbackIso B g).symm))

theorem iteratedActionFamilyIso_hom :
    (iteratedActionFamilyIso A B f h g e).abelian.hom = e.polarized.abelian.hom := by
  change (Over.pullback h).map (𝟙 _) ≫ 𝟙 _ ≫ e.polarized.abelian.hom ≫ 𝟙 _ = _
  rw [(Over.pullback h).map_id, Category.id_comp, Category.id_comp]
  exact Category.comp_id e.polarized.abelian.hom

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IteratedActionFamilyIso.Family
