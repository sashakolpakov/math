import OAI.AlgebraicGeometry.Comparison.Betti.RingModuleStalkFunctor

/-! # Point Module Presheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PointModulePresheaf.Local

noncomputable section

/-! Modules over a ring stalk give actual point-supported module
presheaves. Their sections are values indexed by proofs that the
chosen point belongs to the open set. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} (R : TopCat.Presheaf RingCat.{0} X) (x : X)

def pointModuleSections (N : ModuleCat.{0} (R.stalk x)) (U : Opens X) : ModuleCat.{0} (R.obj (op U)) :=
  let (_h : PLift (x ∈ U)) : Module (R.obj (op U)) N := Module.compHom N (R.germ U x _h.down).hom
  ModuleCat.of (R.obj (op U)) (PLift (x ∈ U) → N)

def pointModulePresheaf (N : ModuleCat.{0} (R.stalk x)) : PresheafOfModules.{0} R where
  obj U := pointModuleSections R x N U.unop
  map {U V} h := ModuleCat.ofHom
    (X := pointModuleSections R x N U.unop)
    (Y := (ModuleCat.restrictScalars (R.map h).hom).obj (pointModuleSections R x N V.unop))
    { toFun a hx := a ⟨leOfHom h.unop hx.down⟩
      map_add' _ _ := rfl
      map_smul' r a := by
        funext hx
        change R.germ U.unop x (leOfHom h.unop hx.down) r • a ⟨leOfHom h.unop hx.down⟩ =
          R.germ V.unop x hx.down (R.map h r) • a ⟨leOfHom h.unop hx.down⟩
        rw [TopCat.Presheaf.germ_res_apply'] }
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext hx
    rfl
  map_comp h k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext hx
    rfl

def pointModulePresheafMap {N N' : ModuleCat.{0} (R.stalk x)} (f : N ⟶ N') :
    pointModulePresheaf R x N ⟶ pointModulePresheaf R x N' where
  app U := ModuleCat.ofHom
    (X := pointModuleSections R x N U.unop) (Y := pointModuleSections R x N' U.unop)
    { toFun a hx := f (a hx)
      map_add' a b := by funext hx; exact map_add f.hom (a hx) (b hx)
      map_smul' r a := by funext hx; exact f.hom.map_smul (R.germ U.unop x hx.down r) (a hx) }
  naturality h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext hx
    rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.PointModulePresheaf.Local
