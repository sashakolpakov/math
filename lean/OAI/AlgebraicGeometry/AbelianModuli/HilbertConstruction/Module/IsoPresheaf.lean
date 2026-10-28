import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoSlicePullback

/-! # Iso Presheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoPresheaf

noncomputable section

/-! Actual module isomorphisms after base change form a presheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (M N : X.Modules)

def moduleIsoPresheaf : (Over X)ᵒᵖ ⥤ Type u where
  obj T := (Scheme.Modules.pullback T.unop.hom).obj M ≅ (Scheme.Modules.pullback T.unop.hom).obj N
  map f := TypeCat.ofHom (IsoSlicePullback.moduleIsoPullbackAlong f.unop)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro e
    exact IsoSlicePullback.moduleIsoPullbackAlong_id T.unop e
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro e
    exact (IsoSlicePullback.moduleIsoPullbackAlong_comp g.unop f.unop e).symm

def moduleIsoHom : moduleIsoPresheaf M N ⟶ HomPresheaf.moduleHomPresheaf M N where
  app _ := TypeCat.ofHom (fun e => e.hom)
  naturality _ _ _ := rfl

def moduleIsoInv : moduleIsoPresheaf M N ⟶ HomPresheaf.moduleHomPresheaf N M where
  app _ := TypeCat.ofHom (fun e => e.inv)
  naturality _ _ _ := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoPresheaf
