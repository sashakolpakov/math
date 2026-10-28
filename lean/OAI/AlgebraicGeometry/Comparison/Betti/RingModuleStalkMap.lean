import Mathlib.Algebra.Category.ModuleCat.Stalk

/-! # Ring Module Stalk Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.RingModuleStalkMap.Local

noncomputable section

/-! Morphisms of actual presheaves of modules induce linear maps on
their stalks over the stalk of the ring presheaf. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} {R : TopCat.Presheaf RingCat.{0} X}
  {M N : PresheafOfModules.{0} R} (f : M ⟶ N) (x : X)

def additiveStalkMap : TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := X) M.presheaf x →+
    TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := X) N.presheaf x :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map ((PresheafOfModules.toPresheaf R).map f)).hom

theorem additiveStalkMap_germ (U : Opens X) (hx : x ∈ U) (m : M.obj (op U)) :
    additiveStalkMap f x (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := X) M.presheaf U x hx m) =
      TopCat.Presheaf.germ (C := AddCommGrpCat) (X := X) N.presheaf U x hx (f.app (op U) m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx ((PresheafOfModules.toPresheaf R).map f) m

theorem stalkMap_smul (r : R.stalk x) (m : TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := X) M.presheaf x) :
    additiveStalkMap f x (r • m) = r • additiveStalkMap f x m := by
  obtain ⟨U, hxU, a, rfl⟩ := R.exists_germ_eq r
  obtain ⟨V, hxV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat) (X := X) M.presheaf m
  change M.obj (op V) at b
  let W := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  have hWU : W ≤ U := inf_le_left
  have hWV : W ≤ V := inf_le_right
  have hr := R.germ_res_apply (homOfLE hWU) x hxW a
  have hm := TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat) (X := X) M.presheaf (homOfLE hWV) x hxW b
  rw [← hr, ← hm]
  erw [← M.germ_ringCat_smul x W hxW (R.map (homOfLE hWU).op a) (M.map (homOfLE hWV).op b)]
  erw [additiveStalkMap_germ, additiveStalkMap_germ]
  change TopCat.Presheaf.germ (C := AddCommGrpCat) (X := X) N.presheaf W x hxW (f.app (op W)
    (R.map (homOfLE hWU).op a • M.map (homOfLE hWV).op b)) = _
  erw [(f.app (op W)).hom.map_smul]
  exact N.germ_ringCat_smul x W hxW (R.map (homOfLE hWU).op a) (f.app (op W) (M.map (homOfLE hWV).op b))

def ringModuleStalkMap : TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := X) M.presheaf x →ₗ[R.stalk x]
    TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := X) N.presheaf x where
  __ := additiveStalkMap f x
  map_smul' r m := stalkMap_smul f x r m

theorem ringModuleStalkMap_germ (U : Opens X) (hx : x ∈ U) (m : M.obj (op U)) :
    ringModuleStalkMap f x (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := X) M.presheaf U x hx m) = TopCat.Presheaf.germ (C := AddCommGrpCat) (X := X) N.presheaf U x hx (f.app (op U) m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx ((PresheafOfModules.toPresheaf R).map f) m

end

end OAI.AlgebraicGeometry.Comparison.Betti.RingModuleStalkMap.Local
