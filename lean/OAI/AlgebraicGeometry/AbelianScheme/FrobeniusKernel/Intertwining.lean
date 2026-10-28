import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Opposites

/-! # Intertwining -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Intertwining.Construction

/-! Composition and change of representation for endomorphism squares. -/

open _root_.CategoryTheory

theorem intertwining_comp {C : Type*} [Category C] {X Y Z : C}
    (a : X ⟶ X) (b : Y ⟶ Y) (c : Z ⟶ Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : a ≫ f = f ≫ b) (hg : b ≫ g = g ≫ c) :
    a ≫ (f ≫ g) = (f ≫ g) ≫ c := by
  rw [← Category.assoc, hf, Category.assoc, hg, ← Category.assoc]

theorem intertwining_inverse {C : Type*} [Category C] {X Y : C}
    (e : X ≅ Y) (a : X ⟶ X) (b : Y ⟶ Y) (h : a ≫ e.hom = e.hom ≫ b) :
    b ≫ e.inv = e.inv ≫ a := by
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, ← h, Category.assoc, e.hom_inv_id, Category.comp_id,
    e.hom_inv_id_assoc]

theorem intertwining_sourceIso {C : Type*} [Category C] {X Y Z : C}
    (e : X ≅ Y) (a : X ⟶ X) (b : Y ⟶ Y) (c : Z ⟶ Z) (f : X ⟶ Z)
    (he : a ≫ e.hom = e.hom ≫ b) (hf : a ≫ f = f ≫ c) :
    b ≫ (e.inv ≫ f) = (e.inv ≫ f) ≫ c :=
  intertwining_comp b a c e.inv f (intertwining_inverse e a b he) hf

theorem intertwining_op_map {C E : Type*} [Category C] [Category E]
    (F : Cᵒᵖ ⥤ E) {X Y : C} (a : X ⟶ X) (b : Y ⟶ Y) (f : X ⟶ Y)
    (h : a ≫ f = f ≫ b) :
    F.map b.op ≫ F.map f.op = F.map f.op ≫ F.map a.op := by
  simpa only [op_comp, Functor.map_comp] using congrArg (fun g => F.map g.op) h.symm

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Intertwining.Construction
