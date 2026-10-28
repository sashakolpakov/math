import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Functor
import OAI.AlgebraicGeometry.Comparison.Betti.PushforwardStalk

/-! # Pushforward Unit -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.PushforwardUnit

noncomputable section

/-! The canonical stalk-family comparison across a continuous map retains the original Godement unit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Presheaf

variable {X Y : TopCat.{0}} (f : Y ⟶ X)

def stalkFamilyPushforwardMap (G : ConstantSheafSections.ComplexSheaves Y) :
    (Functor.stalkFamilyFunctor X).obj ((TopologicalSheafPullback.sheafDirectImage f).obj G) ⟶
      (TopologicalSheafPullback.sheafDirectImage f).obj ((Functor.stalkFamilyFunctor Y).obj G) :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom
        { toFun := fun s y => stalkPushforward (ModuleCat.{0} ℂ) f G.obj y.val
            (s ⟨f y.val, y.property⟩)
          map_add' := by intro s t; funext y; exact map_add _ _ _
          map_smul' := by intro c s; funext y; exact map_smul _ _ _ }
      naturality := by
        intro U V i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        funext y
        rfl }

theorem stalkFamilyPushforwardMap_naturality {G H : ConstantSheafSections.ComplexSheaves Y} (g : G ⟶ H) :
    (Functor.stalkFamilyFunctor X).map ((TopologicalSheafPullback.sheafDirectImage f).map g) ≫ stalkFamilyPushforwardMap f H =
      stalkFamilyPushforwardMap f G ≫ (TopologicalSheafPullback.sheafDirectImage f).map ((Functor.stalkFamilyFunctor Y).map g) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext y
  exact ConcreteCategory.congr_hom (PushforwardStalk.pushforwardStalk_naturality f g.hom y.val)
    (s ⟨f y.val, y.property⟩)

def stalkFamilyPushforwardComparison :
    TopologicalSheafPullback.sheafDirectImage f ⋙ Functor.stalkFamilyFunctor X ⟶
      Functor.stalkFamilyFunctor Y ⋙ TopologicalSheafPullback.sheafDirectImage f where
  app := stalkFamilyPushforwardMap f
  naturality _ _ g := stalkFamilyPushforwardMap_naturality f g

theorem stalkFamilyPushforwardMap_unit (G : ConstantSheafSections.ComplexSheaves Y) :
    (Functor.stalkFamilyUnit X).app ((TopologicalSheafPullback.sheafDirectImage f).obj G) ≫ stalkFamilyPushforwardMap f G =
      (TopologicalSheafPullback.sheafDirectImage f).map ((Functor.stalkFamilyUnit Y).app G) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext y
  exact ConcreteCategory.congr_hom
    (stalkPushforward_germ (ModuleCat.{0} ℂ) f G.obj U.unop y.val y.property) s

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.PushforwardUnit
