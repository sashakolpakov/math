import OAI.AlgebraicGeometry.Comparison.Betti.PointModulePresheaf

/-! # Point Module To Stalk -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PointModuleToStalk.Local

noncomputable section

/-! A morphism to the actual point-supported module determines a
linear map from the module stalk by the neighborhood colimit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} {R : TopCat.Presheaf RingCat.{0} X} (x : X)
  (M : PresheafOfModules.{0} R) (N : ModuleCat.{0} (R.stalk x))

def pointModuleHomCocone (f : M ⟶ PointModulePresheaf.Local.pointModulePresheaf R x N) :
    Cocone ((OpenNhds.inclusion x).op ⋙ M.presheaf) where
  pt := AddCommGrpCat.of N
  ι :=
    { app := fun U => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun m => (f.app (op U.unop.val) m : PointModulePresheaf.Local.pointModuleSections R x N U.unop.val) ⟨U.unop.property⟩)
        (by
          intro m n
          exact congrArg (fun a : PointModulePresheaf.Local.pointModuleSections R x N U.unop.val => a ⟨U.unop.property⟩)
            ((f.app (op U.unop.val)).hom.map_add m n)))
      naturality := by
        intro U V h
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro m
        exact congrArg (fun a : PointModulePresheaf.Local.pointModuleSections R x N V.unop.val => a ⟨V.unop.property⟩)
          (PresheafOfModules.naturality_apply f ((OpenNhds.inclusion x).op.map h) m) }

def pointModuleHomToStalkAdd (f : M ⟶ PointModulePresheaf.Local.pointModulePresheaf R x N) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := X) M.presheaf x →+ N :=
  (colimit.desc _ (pointModuleHomCocone x M N f)).hom

theorem pointModuleHomToStalkAdd_germ (f : M ⟶ PointModulePresheaf.Local.pointModulePresheaf R x N)
    (U : Opens X) (hx : x ∈ U) (m : M.obj (op U)) :
    pointModuleHomToStalkAdd x M N f
      (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := X) M.presheaf U x hx m) =
        (f.app (op U) m : PointModulePresheaf.Local.pointModuleSections R x N U) ⟨hx⟩ :=
  DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
    (colimit.ι_desc (pointModuleHomCocone x M N f) (op ⟨U, hx⟩))) m

theorem pointModuleHomToStalkAdd_smul (f : M ⟶ PointModulePresheaf.Local.pointModulePresheaf R x N) (r : R.stalk x)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := X) M.presheaf x) :
    pointModuleHomToStalkAdd x M N f (r • m) = r • pointModuleHomToStalkAdd x M N f m := by
  obtain ⟨U, hxU, a, rfl⟩ := R.exists_germ_eq r
  obtain ⟨V, hxV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat) (X := X) M.presheaf m
  change M.obj (op V) at b
  let W := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  have hWU : W ≤ U := inf_le_left
  have hWV : W ≤ V := inf_le_right
  have hr := R.germ_res_apply (homOfLE hWU) x hxW a
  have hm := TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat) (X := X) M.presheaf
    (homOfLE hWV) x hxW b
  rw [← hr, ← hm]
  erw [← M.germ_ringCat_smul x W hxW (R.map (homOfLE hWU).op a) (M.map (homOfLE hWV).op b),
    pointModuleHomToStalkAdd_germ, pointModuleHomToStalkAdd_germ]
  exact congrArg (fun v : PointModulePresheaf.Local.pointModuleSections R x N W => v ⟨hxW⟩)
    ((f.app (op W)).hom.map_smul (R.map (homOfLE hWU).op a) (M.map (homOfLE hWV).op b))

def pointModuleHomToStalk (f : M ⟶ PointModulePresheaf.Local.pointModulePresheaf R x N) : (RingModuleStalkFunctor.Local.ringModuleStalk R x).obj M ⟶ N :=
  ModuleCat.ofHom
    { __ := pointModuleHomToStalkAdd x M N f
      map_smul' r m := pointModuleHomToStalkAdd_smul x M N f r m }

end

end OAI.AlgebraicGeometry.Comparison.Betti.PointModuleToStalk.Local
