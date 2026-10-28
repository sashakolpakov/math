import OAI.AlgebraicGeometry.Comparison.Betti.Module.RingedStalkPushforward

/-! # Point Module Pushforward -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PointModulePushforward.Local

noncomputable section

section

/-! Direct image of a point-supported module is restriction of scalars
along the actual native ring-stalk map. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
  {R : TopCat.Presheaf RingCat.{0} X} {S : TopCat.Presheaf RingCat.{0} Y}
  (φ : S ⟶ (Opens.map f).op ⋙ R) (x : X)

def pointModulePushforwardSections (N : ModuleCat.{0} (R.stalk x)) (U : Opens Y) :
    ((PresheafOfModules.pushforward φ).obj (PointModulePresheaf.Local.pointModulePresheaf R x N)).obj (op U) ≅
      PointModulePresheaf.Local.pointModuleSections S (f x) ((ModuleCat.restrictScalars (Module.RingedStalkPushforward.Local.ringedStalkMap f φ x)).obj N) U := by
  let A : ModuleCat (S.obj (op U)) :=
    ((PresheafOfModules.pushforward φ).obj (PointModulePresheaf.Local.pointModulePresheaf R x N)).obj (op U)
  let B : ModuleCat (S.obj (op U)) :=
    PointModulePresheaf.Local.pointModuleSections S (f x) ((ModuleCat.restrictScalars (Module.RingedStalkPushforward.Local.ringedStalkMap f φ x)).obj N) U
  exact (show A ≃ₗ[S.obj (op U)] B from
    { toFun := fun a hx => a hx
      invFun := fun a hx => a hx
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r a
        funext hx
        change R.germ ((Opens.map f).obj U) x hx.down (φ.app (op U) r) • a hx =
          Module.RingedStalkPushforward.Local.ringedStalkMap f φ x (S.germ U (f x) hx.down r) • a hx
        rw [Module.RingedStalkPushforward.Local.ringedStalkMap_germ] }).toModuleIso

def pointModulePresheafPushforwardIso (N : ModuleCat.{0} (R.stalk x)) :
    (PresheafOfModules.pushforward φ).obj (PointModulePresheaf.Local.pointModulePresheaf R x N) ≅
      PointModulePresheaf.Local.pointModulePresheaf S (f x) ((ModuleCat.restrictScalars (Module.RingedStalkPushforward.Local.ringedStalkMap f φ x)).obj N) :=
  PresheafOfModules.isoMk (fun U => pointModulePushforwardSections f φ x N U.unop) (by
    intro U V h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext hx
    rfl)

def pointModulePresheafPushforward :
    PointModuleFunctor.Local.pointModulePresheafFunctor R x ⋙ PresheafOfModules.pushforward φ ≅
      ModuleCat.restrictScalars (Module.RingedStalkPushforward.Local.ringedStalkMap f φ x) ⋙ PointModuleFunctor.Local.pointModulePresheafFunctor S (f x) :=
  NatIso.ofComponents (pointModulePresheafPushforwardIso f φ x) (by
    intro N N' g
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext hx
    rfl)

end

/-! The native sheaf direct image carries point-supported modules to
the modules obtained by restriction along the native stalk map. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}
  {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{0}}
  [(Opens.map f).IsContinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)]
  (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R) (x : X)

def pointModuleSheafPushforwardIso
    (N : ModuleCat.{0} (TopCat.Presheaf.stalk (C := RingCat) (X := X) R.obj x)) :
    (SheafOfModules.pushforward φ).obj ((PointModuleFunctor.Local.pointModuleSheafFunctor R x).obj N) ≅
      (PointModuleFunctor.Local.pointModuleSheafFunctor S (f x)).obj
        ((ModuleCat.restrictScalars (Module.RingedStalkPushforward.Local.ringedStalkMap f φ.hom x)).obj N) :=
  (SheafOfModules.fullyFaithfulForget S).preimageIso
    (pointModulePresheafPushforwardIso f φ.hom x N)

def pointModuleSheafPushforward :
    PointModuleFunctor.Local.pointModuleSheafFunctor R x ⋙ SheafOfModules.pushforward φ ≅
      ModuleCat.restrictScalars (Module.RingedStalkPushforward.Local.ringedStalkMap f φ.hom x) ⋙ PointModuleFunctor.Local.pointModuleSheafFunctor S (f x) :=
  NatIso.ofComponents (pointModuleSheafPushforwardIso f φ x) (by
    intro N N' g
    apply SheafOfModules.Hom.ext
    exact (pointModulePresheafPushforward f φ.hom x).hom.naturality g)

end

end OAI.AlgebraicGeometry.Comparison.Betti.PointModulePushforward.Local
