import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange

/-! # Albanese Base Change Comp -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseBaseChangeComp

noncomputable section

/-! Group-preserving comparison of single and iterated base changes for
all the actual Albanese groups, without dimension data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S T U : Scheme.{u}} (A : Over S) [GrpObj A]

def pullbackCompositionGroupIso (f : U ⟶ T) (g : T ⟶ S) :
    Grp.mk ((Over.pullback (f ≫ g)).obj A) ≅
      Grp.mk ((Over.pullback f).obj ((Over.pullback g).obj A)) :=
  (Functor.mapGrpNatIso (Over.pullbackComp f g)).app (Grp.mk A) ≪≫
    (Functor.mapGrpCompIso (F := Over.pullback g) (G := Over.pullback f)).app (Grp.mk A)

abbrev pullbackCompositionIso (f : U ⟶ T) (g : T ⟶ S) :
    (Over.pullback (f ≫ g)).obj A ≅ (Over.pullback f).obj ((Over.pullback g).obj A) :=
  (Grp.forget (Over U)).mapIso (pullbackCompositionGroupIso A f g)

instance pullbackCompositionIso_isMonHom (f : U ⟶ T) (g : T ⟶ S) :
    IsMonHom (pullbackCompositionIso A f g).hom :=
  (pullbackCompositionGroupIso A f g).hom.hom.isMonHom_hom

@[simp] theorem pullbackCompositionIso_hom (f : U ⟶ T) (g : T ⟶ S) :
    (pullbackCompositionIso A f g).hom = (Over.pullbackComp f g).hom.app A := by
  change (Over.pullbackComp f g).hom.app A ≫ 𝟙 _ = _
  exact Category.comp_id _

@[simp] theorem pullbackCompositionIso_inv (f : U ⟶ T) (g : T ⟶ S) :
    (pullbackCompositionIso A f g).inv = (Over.pullbackComp f g).inv.app A := by
  change 𝟙 _ ≫ (Over.pullbackComp f g).inv.app A = _
  exact Category.id_comp _

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseBaseChangeComp
