import OAI.AlgebraicGeometry.Picard.Homomorphisms.InternalHomUnit

/-! # Internal Hom Maps -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.InternalHomMaps

noncomputable section

/-! Functoriality of the constructed internal Hom. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} {K L M N P Q : X.Modules}

def moduleInternalHomMap (f : L ⟶ M) (g : N ⟶ P) :
    InternalHom.Construction.moduleInternalHom M N ⟶ InternalHom.Construction.moduleInternalHom L P :=
  TensorHom.Construction.sheafBilinearCurry
    (((TensorHom.Construction.sheafBilinearUncurry (𝟙 (InternalHom.Construction.moduleInternalHom M N))).precomp (𝟙 _) f).postcomp g)

theorem moduleInternalHomMap_app (f : L ⟶ M) (g : N ⟶ P) (U : X.Opens)
    (a : Γ(InternalHom.Construction.moduleInternalHom M N, U)) (V : Over U) (s : Γ(L, V.left)) :
    ((moduleInternalHomMap f g).app U a).val.app (.op V) s =
      g.app V.left (a.val.app (.op V) (f.app V.left s)) := rfl

theorem moduleInternalHomMap_id (M N : X.Modules) :
    moduleInternalHomMap (𝟙 M) (𝟙 N) = 𝟙 (InternalHom.Construction.moduleInternalHom M N) := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.ext
  intro a
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro s
  rfl

theorem moduleInternalHomMap_comp (f : L ⟶ M) (f' : K ⟶ L) (g : N ⟶ P) (g' : P ⟶ Q) :
    moduleInternalHomMap f g ≫ moduleInternalHomMap f' g' =
      moduleInternalHomMap (f' ≫ f) (g ≫ g') := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.ext
  intro a
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro s
  rfl

def moduleInternalHomCongr (e : M ≅ L) (f : N ≅ P) :
    InternalHom.Construction.moduleInternalHom M N ≅ InternalHom.Construction.moduleInternalHom L P where
  hom := moduleInternalHomMap e.inv f.hom
  inv := moduleInternalHomMap e.hom f.inv
  hom_inv_id := by rw [moduleInternalHomMap_comp, e.hom_inv_id, f.hom_inv_id,
    moduleInternalHomMap_id]
  inv_hom_id := by rw [moduleInternalHomMap_comp, e.inv_hom_id, f.inv_hom_id,
    moduleInternalHomMap_id]

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.InternalHomMaps
