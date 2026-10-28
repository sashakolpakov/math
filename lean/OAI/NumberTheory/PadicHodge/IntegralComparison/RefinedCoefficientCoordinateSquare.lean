import Mathlib.CategoryTheory.Functor.Category

/-! # Refined Coefficient Coordinate Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RefinedCoefficientCoordinateSquare

noncomputable section

/-! A coordinate square remains the same actual morphism after
coefficient change and two compatible refinements. -/

open _root_.CategoryTheory

theorem square {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    {P Q R S T : A} {P' Q' R' : B}
    (a : P ⟶ Q) (b : Q ⟶ R) (s : R ≅ S) (t : P ≅ T) (c : T ⟶ S)
    (eP : F.obj P ≅ P') (eQ : F.obj Q ≅ Q') (eR : F.obj R ≅ R')
    (a' : P' ⟶ Q') (b' : Q' ⟶ R')
    (ha : F.map a ≫ eQ.hom = eP.hom ≫ a')
    (hb : F.map b ≫ eR.hom = eQ.hom ≫ b')
    (hc : a ≫ b ≫ s.hom = t.hom ≫ c) :
    (F.map t.inv ≫ eP.hom) ≫ a' ≫ b' ≫ (eR.inv ≫ F.map s.hom) = F.map c := by
  calc
    _ = F.map t.inv ≫ ((eP.hom ≫ a') ≫ b') ≫ eR.inv ≫ F.map s.hom := by
      simp only [Category.assoc]
    _ = F.map t.inv ≫ ((F.map a ≫ eQ.hom) ≫ b') ≫ eR.inv ≫ F.map s.hom := by
      rw [← ha]
    _ = F.map t.inv ≫ (F.map a ≫ (eQ.hom ≫ b')) ≫ eR.inv ≫ F.map s.hom := by
      simp only [Category.assoc]
    _ = F.map t.inv ≫ (F.map a ≫ (F.map b ≫ eR.hom)) ≫ eR.inv ≫ F.map s.hom := by
      rw [← hb]
    _ = F.map (t.inv ≫ a ≫ b ≫ s.hom) := by
      simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
    _ = F.map c := by rw [hc]; simp only [Iso.inv_hom_id_assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RefinedCoefficientCoordinateSquare
