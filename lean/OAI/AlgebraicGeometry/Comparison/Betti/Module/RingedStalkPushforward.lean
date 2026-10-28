import OAI.AlgebraicGeometry.Comparison.Betti.PointModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import OAI.AlgebraicGeometry.Comparison.Betti.RingModuleStalkFunctor

/-! # Ringed Stalk Pushforward -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.RingedStalkPushforward.Local

noncomputable section

section

/-! The map of native ring stalks induced by a continuous map and a
morphism into the direct image, with its formula on every section. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
  {R : TopCat.Presheaf RingCat.{0} X} {S : TopCat.Presheaf RingCat.{0} Y}
  (φ : S ⟶ (Opens.map f).op ⋙ R) (x : X)

def ringedStalkMap : S.stalk (f x) →+* R.stalk x :=
  ((TopCat.Presheaf.stalkFunctor RingCat (f x)).map φ ≫
    TopCat.Presheaf.stalkPushforward RingCat f R x).hom

theorem ringedStalkMap_germ (U : Opens Y) (hx : f x ∈ U) (s : S.obj (op U)) :
    ringedStalkMap f φ x (S.germ U (f x) hx s) =
      R.germ ((Opens.map f).obj U) x hx (φ.app (op U) s) := by
  change TopCat.Presheaf.stalkPushforward RingCat f R x
    ((TopCat.Presheaf.stalkFunctor RingCat (f x)).map φ (S.germ U (f x) hx s)) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact ConcreteCategory.congr_hom
    (TopCat.Presheaf.stalkPushforward_germ RingCat f R U x hx) (φ.app (op U) s)

end

section

/-! The actual stalk map for module pushforward is semilinear over the original ringed stalk map. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
  {R : TopCat.Presheaf RingCat.{0} X} {S : TopCat.Presheaf RingCat.{0} Y}
  (φ : S ⟶ (Opens.map f).op ⋙ R) (M : PresheafOfModules.{0} R) (x : X)

def modulePushforwardAdditiveStalkMap :
    TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := Y)
      ((PresheafOfModules.pushforward φ).obj M).presheaf (f x) →+
    TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := X) M.presheaf x :=
  (TopCat.Presheaf.stalkPushforward AddCommGrpCat f M.presheaf x).hom

theorem modulePushforwardAdditiveStalkMap_germ (U : Opens Y) (hx : f x ∈ U)
    (m : ((PresheafOfModules.pushforward φ).obj M).obj (op U)) :
    modulePushforwardAdditiveStalkMap f φ M x
      (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := Y)
        ((PresheafOfModules.pushforward φ).obj M).presheaf U (f x) hx m) =
    TopCat.Presheaf.germ (C := AddCommGrpCat) (X := X) M.presheaf
      ((Opens.map f).obj U) x hx m :=
  ConcreteCategory.congr_hom (TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat f M.presheaf U x hx) m

theorem modulePushforwardAdditiveStalkMap_smul
    (r : S.stalk (f x))
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := Y)
      ((PresheafOfModules.pushforward φ).obj M).presheaf (f x)) :
    modulePushforwardAdditiveStalkMap f φ M x (r • m) =
      ringedStalkMap f φ x r • modulePushforwardAdditiveStalkMap f φ M x m := by
  let P := (PresheafOfModules.pushforward φ).obj M
  obtain ⟨U, hxU, a, rfl⟩ := S.exists_germ_eq r
  obtain ⟨V, hxV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat) (X := Y) P.presheaf m
  change P.obj (op V) at b
  let W := U ⊓ V
  have hxW : f x ∈ W := ⟨hxU, hxV⟩
  have hWU : W ≤ U := inf_le_left
  have hWV : W ≤ V := inf_le_right
  have hr := S.germ_res_apply (homOfLE hWU) (f x) hxW a
  have hm := TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat) (X := Y)
    P.presheaf (homOfLE hWV) (f x) hxW b
  rw [← hr, ← hm]
  erw [← P.germ_ringCat_smul (f x) W hxW (S.map (homOfLE hWU).op a) (P.map (homOfLE hWV).op b)]
  erw [modulePushforwardAdditiveStalkMap_germ, ringedStalkMap_germ,
    modulePushforwardAdditiveStalkMap_germ]
  exact M.germ_ringCat_smul x ((Opens.map f).obj W) hxW
    (φ.app (op W) (S.map (homOfLE hWU).op a)) (P.map (homOfLE hWV).op b)

def ringModulePushforwardStalkMap :
    TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := Y)
      ((PresheafOfModules.pushforward φ).obj M).presheaf (f x) →ₛₗ[ringedStalkMap f φ x]
    TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := X) M.presheaf x where
  __ := modulePushforwardAdditiveStalkMap f φ M x
  map_smul' := modulePushforwardAdditiveStalkMap_smul f φ M x

theorem ringModulePushforwardStalkMap_bijective (hf : Topology.IsInducing f) :
    Function.Bijective (ringModulePushforwardStalkMap f φ M x) := by
  let : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat f M.presheaf x) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat hf M.presheaf x
  exact ConcreteCategory.bijective_of_isIso
    (TopCat.Presheaf.stalkPushforward AddCommGrpCat f M.presheaf x)

theorem ringModulePushforwardStalkMap_naturality {N : PresheafOfModules.{0} R} (g : M ⟶ N)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := Y)
      ((PresheafOfModules.pushforward φ).obj M).presheaf (f x)) :
    ringModulePushforwardStalkMap f φ N x
        (RingModuleStalkMap.Local.ringModuleStalkMap ((PresheafOfModules.pushforward φ).map g) (f x) m) =
      RingModuleStalkMap.Local.ringModuleStalkMap g x (ringModulePushforwardStalkMap f φ M x m) := by
  obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat) (X := Y)
    ((PresheafOfModules.pushforward φ).obj M).presheaf m
  erw [RingModuleStalkMap.Local.ringModuleStalkMap_germ]
  change modulePushforwardAdditiveStalkMap f φ N x _ =
    RingModuleStalkMap.Local.ringModuleStalkMap g x (modulePushforwardAdditiveStalkMap f φ M x _)
  erw [modulePushforwardAdditiveStalkMap_germ, modulePushforwardAdditiveStalkMap_germ,
    RingModuleStalkMap.Local.ringModuleStalkMap_germ]
  rfl

end

/-! At an embedded point, native module pushforward stalks are restriction of scalars along the actual ring map. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
  {R : TopCat.Presheaf RingCat.{0} X} {S : TopCat.Presheaf RingCat.{0} Y}
  (φ : S ⟶ (Opens.map f).op ⋙ R) (x : X)

def modulePushforwardStalkHom (M : PresheafOfModules.{0} R) :
    (RingModuleStalkFunctor.Local.ringModuleStalk S (f x)).obj ((PresheafOfModules.pushforward φ).obj M) ⟶
      (ModuleCat.restrictScalars (ringedStalkMap f φ x)).obj ((RingModuleStalkFunctor.Local.ringModuleStalk R x).obj M) :=
  ModuleCat.ofHom (R := S.stalk (f x))
    (X := (RingModuleStalkFunctor.Local.ringModuleStalk S (f x)).obj ((PresheafOfModules.pushforward φ).obj M))
    (Y := (ModuleCat.restrictScalars (ringedStalkMap f φ x)).obj ((RingModuleStalkFunctor.Local.ringModuleStalk R x).obj M))
    { toFun := ringModulePushforwardStalkMap f φ M x
      map_add' := (ringModulePushforwardStalkMap f φ M x).map_add
      map_smul' := (ringModulePushforwardStalkMap f φ M x).map_smul' }

def modulePushforwardStalkNatTrans :
    PresheafOfModules.pushforward φ ⋙ RingModuleStalkFunctor.Local.ringModuleStalk S (f x) ⟶
      RingModuleStalkFunctor.Local.ringModuleStalk R x ⋙ ModuleCat.restrictScalars (ringedStalkMap f φ x) where
  app := modulePushforwardStalkHom f φ x
  naturality {M N} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact ringModulePushforwardStalkMap_naturality f φ M x g m

def modulePushforwardStalkIso (hf : Topology.IsInducing f) :
    PresheafOfModules.pushforward φ ⋙ RingModuleStalkFunctor.Local.ringModuleStalk S (f x) ≅
      RingModuleStalkFunctor.Local.ringModuleStalk R x ⋙ ModuleCat.restrictScalars (ringedStalkMap f φ x) := by
  have (M : PresheafOfModules.{0} R) : IsIso ((modulePushforwardStalkNatTrans f φ x).app M) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ringModulePushforwardStalkMap_bijective f φ M x hf
  exact NatIso.ofComponents (fun M => asIso ((modulePushforwardStalkNatTrans f φ x).app M))
    (fun g => (modulePushforwardStalkNatTrans f φ x).naturality g)

theorem modulePushforwardStalkIso_germ (hf : Topology.IsInducing f)
    (M : PresheafOfModules.{0} R) (U : Opens Y) (hx : f x ∈ U)
    (m : ((PresheafOfModules.pushforward φ).obj M).obj (op U)) :
    (modulePushforwardStalkIso f φ x hf).hom.app M
      (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := Y)
        ((PresheafOfModules.pushforward φ).obj M).presheaf U (f x) hx m) =
    TopCat.Presheaf.germ (C := AddCommGrpCat) (X := X) M.presheaf
      ((Opens.map f).obj U) x hx m :=
  modulePushforwardAdditiveStalkMap_germ f φ M x U hx m

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.RingedStalkPushforward.Local
