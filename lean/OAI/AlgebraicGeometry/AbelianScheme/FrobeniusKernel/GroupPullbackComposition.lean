import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange

/-! # Group Pullback Composition -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GroupPullbackComposition.Construction

noncomputable section

/-! The canonical double-pullback comparison retains the native group law
and its literal underlying scheme morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

attribute [local instance] BaseChange.Construction.pulledBackGroup

def groupPullbackCompIso {S T U : Scheme.{u}} (f : U ⟶ T) (g : T ⟶ S) :
    (Over.pullback (f ≫ g)).mapGrp ≅ (Over.pullback g).mapGrp ⋙ (Over.pullback f).mapGrp :=
  Functor.mapGrpNatIso (Over.pullbackComp f g) ≪≫
    Functor.mapGrpCompIso (F := Over.pullback g) (G := Over.pullback f)

theorem groupPullbackCompIso_hom {S T U : Scheme.{u}} (f : U ⟶ T) (g : T ⟶ S)
    (G : Grp (Over S)) :
    ((groupPullbackCompIso f g).hom.app G).hom.hom = (Over.pullbackComp f g).hom.app G.X :=
  Category.comp_id _

theorem groupPullbackCompIso_inv {S T U : Scheme.{u}} (f : U ⟶ T) (g : T ⟶ S)
    (G : Grp (Over S)) :
    ((groupPullbackCompIso f g).inv.app G).hom.hom = (Over.pullbackComp f g).inv.app G.X :=
  Category.id_comp _

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GroupPullbackComposition.Construction
