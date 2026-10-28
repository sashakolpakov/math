import Mathlib.CategoryTheory.Iso

/-! # Normalized Class Transfer -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NormalizedClassTransfer

/-! A normalized source coordinate and an actual comparison square
identify the original transferred class after a local-to-global map. -/
open _root_.CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] {A B D E F G H : C}

theorem comparison (coordinate : A ⟶ B) (localize : B ⟶ D)
    (transfer : D ⟶ E) (globalize : E ⟶ F) (sourceClass : B ⟶ G)
    (genericTransfer : G ⟶ F) (sourceIso : A ≅ G) (targetIso : H ≅ F)
    (nativeTransfer : A ⟶ H)
    (hlocal : (localize ≫ transfer) ≫ globalize = sourceClass ≫ genericTransfer)
    (hsource : coordinate ≫ sourceClass = sourceIso.hom)
    (htransfer : nativeTransfer ≫ targetIso.hom = sourceIso.hom ≫ genericTransfer) :
    (coordinate ≫ localize ≫ transfer) ≫ globalize ≫ targetIso.inv = nativeTransfer := by
  calc
    _ = coordinate ≫ ((localize ≫ transfer) ≫ globalize) ≫ targetIso.inv := by
      simp only [Category.assoc]
    _ = coordinate ≫ (sourceClass ≫ genericTransfer) ≫ targetIso.inv := by rw [hlocal]
    _ = (coordinate ≫ sourceClass) ≫ genericTransfer ≫ targetIso.inv := by
      simp only [Category.assoc]
    _ = sourceIso.hom ≫ genericTransfer ≫ targetIso.inv := by rw [hsource]
    _ = (nativeTransfer ≫ targetIso.hom) ≫ targetIso.inv := by
      rw [htransfer]
      simp only [Category.assoc]
    _ = nativeTransfer := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end OAI.NumberTheory.PadicHodge.IntegralComparison.NormalizedClassTransfer
