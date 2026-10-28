import OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness

/-! # Coefficient Diagram Two -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientDiagramTwo.CoefficientDiagram

/-! Small categorical diagram chases used in native coefficient comparisons. -/

open _root_.CategoryTheory

theorem map_square {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B B' E : C} (a : A ⟶ B) (b : B ⟶ E) (c : A ⟶ B') (d : B' ⟶ E)
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d :=
  (F.map_comp a b).symm.trans ((congrArg F.map h).trans (F.map_comp c d))

theorem unit_image_comp {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {P : D} {A B E : C} (η : P ⟶ F.obj A) (a : A ⟶ B) (b : B ⟶ E) :
    η ≫ F.map (a ≫ b) = (η ≫ F.map a) ≫ F.map b := by
  rw [F.map_comp, Category.assoc]

theorem two_step_square {C : Type*} [Category* C] {A B D E F G H : C}
    (p : A ⟶ B) (η : B ⟶ D) (u : D ⟶ E) (x : B ⟶ F) (v : F ⟶ E)
    (q : A ⟶ G) (θ : G ⟶ H) (w : H ⟶ E) (y : G ⟶ F)
    (hη : η ≫ u = x ≫ v) (hθ : θ ≫ w = y ≫ v) (hp : p ≫ x = q ≫ y) :
    (p ≫ η) ≫ u = (q ≫ θ) ≫ w := by
  rw [Category.assoc, hη, ← Category.assoc, hp, Category.assoc, ← hθ, ← Category.assoc]

theorem mate_paste {C : Type*} [Category* C] {A B D E F G : C}
    (d : A ⟶ B) (ηX : B ⟶ D) (ηY : A ⟶ E) (a : E ⟶ D)
    (b : D ⟶ F) (c : E ⟶ G) (t : G ⟶ F)
    (hu : d ≫ ηX = ηY ≫ a) (hs : a ≫ b = c ≫ t) :
    d ≫ ηX ≫ b = (ηY ≫ c) ≫ t := by
  rw [← Category.assoc, hu, Category.assoc, hs, ← Category.assoc]

theorem inverse_left_square {C : Type*} [Category* C] {A B D : C}
    (e : A ≅ B) (a : A ⟶ D) (b : B ⟶ D) (h : a = e.hom ≫ b) :
    b = e.inv ≫ a := by
  rw [h, Iso.inv_hom_id_assoc]

end OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientDiagramTwo.CoefficientDiagram
