import OAI.AlgebraicGeometry.Comparison.Betti.PointModuleFunctor

/-! # Stalk To Point Module -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.StalkToPointModule.Local

noncomputable section

/-! A linear map from an actual module stalk gives a morphism to the
actual point-supported module sheaf, by applying it to section germs. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} {R : TopCat.Presheaf RingCat.{0} X} (x : X)
  (M : PresheafOfModules.{0} R) (N : ModuleCat.{0} (R.stalk x))

def stalkToPointModuleHom (f : (RingModuleStalkFunctor.Local.ringModuleStalk R x).obj M ⟶ N) :
    M ⟶ PointModulePresheaf.Local.pointModulePresheaf R x N where
  app U := ModuleCat.ofHom
    (X := M.obj U) (Y := PointModulePresheaf.Local.pointModuleSections R x N U.unop)
    { toFun m hx := f (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := X) M.presheaf U.unop x hx.down m)
      map_add' m n := by
        funext hx
        exact (congrArg f (map_add (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := X)
          M.presheaf U.unop x hx.down).hom m n)).trans (map_add f.hom _ _)
      map_smul' r m := by
        funext hx
        exact (congrArg f (M.germ_ringCat_smul x U.unop hx.down r m)).trans (f.hom.map_smul _ _) }
  naturality {U V} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    funext hx
    exact congrArg f (TopCat.Presheaf.germ_res_apply' (C := AddCommGrpCat) (X := X) M.presheaf h x hx.down m)

theorem stalkToPointModuleHom_apply (f : (RingModuleStalkFunctor.Local.ringModuleStalk R x).obj M ⟶ N)
    (U : Opens X) (m : M.obj (op U)) (hx : x ∈ U) :
    (stalkToPointModuleHom x M N f).app (op U) m ⟨hx⟩ =
      f (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := X) M.presheaf U x hx m) := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.StalkToPointModule.Local
