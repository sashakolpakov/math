import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleBlockBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.BaseChangeComparisons

/-! # Split Block Pullback -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitBlockPullback

noncomputable section

/-! Transport an actual ordinary product splitting through a commuting
base-change square, retaining the original finite constant factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleBlockBaseChange

variable {S T U : Scheme} (A : Grp (Over S))
  (f : T ⟶ S) (h : U ⟶ T) (g : U ⟶ S) (w : h ≫ f = g)

def iteratedBlockGroupIso :
    (Over.pullback h).mapGrp.obj ((Over.pullback f).mapGrp.obj A) ≅
      (Over.pullback g).mapGrp.obj A := by
  let : GrpObj ((Over.pullback f).obj A.X) := Functor.grpObjObj (F := Over.pullback f)
  let : GrpObj ((Over.pullback h).obj ((Over.pullback f).obj A.X)) :=
    Functor.grpObjObj (F := Over.pullback h)
  let : GrpObj ((Over.pullback g).obj A.X) := Functor.grpObjObj (F := Over.pullback g)
  exact Grp.mkIso' (PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso A.X f h g w)

variable (M : Grp (Over T)) (G : Type) [Group G]
  (e : (Over.pullback f).mapGrp.obj A ≅ M ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme T G)

def splitBlockPullbackIso :
    (Over.pullback g).mapGrp.obj A ≅
      (Over.pullback h).mapGrp.obj M ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme U G :=
  (iteratedBlockGroupIso A f h g w).symm ≪≫
    (Over.pullback h).mapGrp.mapIso e ≪≫
      (Functor.Monoidal.μIso (Over.pullback h).mapGrp M (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme T G)).symm ≪≫
        tensorIso (Iso.refl _) (EtaleBlockBaseChange.etaleBlockBaseChangeIso h G)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitBlockPullback
