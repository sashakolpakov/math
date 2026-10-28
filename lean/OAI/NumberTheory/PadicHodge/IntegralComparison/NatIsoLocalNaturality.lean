import Mathlib.CategoryTheory.NatIso

/-! # Nat Iso Local Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NatIsoLocalNaturality

/-! A local naturality square is preserved by the given natural isomorphisms. -/

open _root_.CategoryTheory

variable {C A : Type*} [Category* C] [Category* A] {F F' G G' : C ⥤ A}
  (eF : F ≅ F') (eG : G ≅ G') {c d : C} (f : c ⟶ d)
  (a : F.obj c ⟶ G.obj c) (b : F.obj d ⟶ G.obj d)

theorem square (h : F.map f ≫ b = a ≫ G.map f) :
    F'.map f ≫ (eF.app d).inv ≫ b ≫ (eG.app d).hom =
      (eF.app c).inv ≫ a ≫ (eG.app c).hom ≫ G'.map f := by
  calc
    _ = (F'.map f ≫ (eF.app d).inv) ≫ b ≫ (eG.app d).hom := by simp only [Category.assoc]
    _ = ((eF.app c).inv ≫ F.map f) ≫ b ≫ (eG.app d).hom :=
      congrArg (fun t => t ≫ b ≫ (eG.app d).hom) (eF.inv.naturality f)
    _ = (eF.app c).inv ≫ (F.map f ≫ b) ≫ (eG.app d).hom := by simp only [Category.assoc]
    _ = (eF.app c).inv ≫ (a ≫ G.map f) ≫ (eG.app d).hom := by rw [h]
    _ = (eF.app c).inv ≫ a ≫ (G.map f ≫ (eG.app d).hom) := by simp only [Category.assoc]
    _ = (eF.app c).inv ≫ a ≫ (eG.app c).hom ≫ G'.map f :=
      congrArg (fun t => (eF.app c).inv ≫ a ≫ t) (eG.hom.naturality f)

end OAI.NumberTheory.PadicHodge.IntegralComparison.NatIsoLocalNaturality
