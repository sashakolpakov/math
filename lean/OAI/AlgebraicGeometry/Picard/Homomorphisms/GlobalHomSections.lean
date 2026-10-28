import OAI.AlgebraicGeometry.Picard.Homomorphisms.InternalHom
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Global Hom Sections -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.GlobalHomSections

noncomputable section

/-! Global sections of the constructed internal Hom are the actual
module-sheaf morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} (M N : X.Modules)

def moduleHomGlobalSection (b : M ⟶ N) : Γ(InternalHom.Construction.moduleInternalHom M N, ⊤) :=
  ⟨Functor.whiskerLeft (Over.forget (⊤ : X.Opens)).op b.mapPresheaf,
    fun _ r s => b.app_smul r s⟩

def moduleHomOfGlobalSection (a : Γ(InternalHom.Construction.moduleInternalHom M N, ⊤)) : M ⟶ N where
  val.app U := ModuleCat.ofHom
    { toFun := a.val.app (op (Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top))))
      map_add' r s := map_add (a.val.app (op (Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top))))).hom r s
      map_smul' r s := a.property (Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top))) r s }
  val.naturality {U V} j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    let j' : Over.mk (homOfLE (show V.unop ≤ ⊤ from le_top)) ⟶
        Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top)) := Over.homMk j.unop
    exact ConcreteCategory.congr_hom (a.val.naturality j'.op) s

def moduleHomGlobalSectionEquiv : (M ⟶ N) ≃ Γ(InternalHom.Construction.moduleInternalHom M N, ⊤) where
  toFun := moduleHomGlobalSection M N
  invFun := moduleHomOfGlobalSection M N
  left_inv b := by
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    rfl
  right_inv a := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.ext
    intro s
    have hv : Over.mk (homOfLE (show V.unop.left ≤ (⊤ : X.Opens) from le_top)) = V.unop := by
      cases V.unop
      congr
    change a.val.app (op (Over.mk (homOfLE (show V.unop.left ≤ ⊤ from le_top)))) s = a.val.app V s
    cases V
    cases hv
    rfl

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.GlobalHomSections
