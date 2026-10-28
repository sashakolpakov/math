import Mathlib.CategoryTheory.Iso

/-! # Retract Iso -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.RetractIso

/-! An isomorphism respecting two split projectors restricts to an
isomorphism of their actual retracts. -/

open _root_.CategoryTheory

variable {C : Type*} [Category C] {X Y A B : C}
  (e : X ≅ Y) (iA : A ⟶ X) (rA : X ⟶ A) (iB : B ⟶ Y) (rB : Y ⟶ B)
  (hA : iA ≫ rA = 𝟙 A) (hB : iB ≫ rB = 𝟙 B)
  (hp : (rA ≫ iA) ≫ e.hom = e.hom ≫ (rB ≫ iB))

include hA hp in
theorem retractIso_forward_inverse :
    (iA ≫ e.hom ≫ rB) ≫ (iB ≫ e.inv ≫ rA) = 𝟙 A := by
  calc
    _ = iA ≫ (e.hom ≫ (rB ≫ iB)) ≫ e.inv ≫ rA := by simp only [Category.assoc]
    _ = iA ≫ ((rA ≫ iA) ≫ e.hom) ≫ e.inv ≫ rA := by rw [hp]
    _ = (iA ≫ rA) ≫ (iA ≫ rA) := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = 𝟙 A := by rw [hA, Category.id_comp]

include hB hp in
theorem retractIso_inverse_forward :
    (iB ≫ e.inv ≫ rA) ≫ (iA ≫ e.hom ≫ rB) = 𝟙 B := by
  calc
    _ = iB ≫ e.inv ≫ ((rA ≫ iA) ≫ e.hom) ≫ rB := by simp only [Category.assoc]
    _ = iB ≫ e.inv ≫ (e.hom ≫ (rB ≫ iB)) ≫ rB := by rw [hp]
    _ = (iB ≫ rB) ≫ (iB ≫ rB) := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = 𝟙 B := by rw [hB, Category.id_comp]

def isoOfCompatibleRetracts : A ≅ B where
  hom := iA ≫ e.hom ≫ rB
  inv := iB ≫ e.inv ≫ rA
  hom_inv_id := retractIso_forward_inverse e iA rA iB rB hA hp
  inv_hom_id := retractIso_inverse_forward e iA rA iB rB hB hp

end OAI.AlgebraicGeometry.PELModuli.CMPoints.RetractIso
