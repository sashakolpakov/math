import Mathlib.CategoryTheory.Iso

/-! # Inverse Model Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InverseModelFactorization

noncomputable section

/-! Transporting a factorization back through compatible model isomorphisms preserves its equation and invertible projection. -/

open _root_.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]
variable {X Z A X' Z' A' : C} (eX : X' ≅ X) (eZ : Z' ≅ Z)

def modelFactorizationMap (h : X ⟶ Z) : X' ⟶ Z' := eX.hom ≫ h ≫ eZ.inv

theorem modelFactorizationMap_comp (eA : A' ≅ A) (h : X ⟶ Z) (p : Z ⟶ A) (p' : Z' ⟶ A')
    (hp : eZ.hom ≫ p = p' ≫ eA.hom) :
    modelFactorizationMap eX eZ h ≫ p' = eX.hom ≫ (h ≫ p) ≫ eA.inv := by
  apply (cancel_mono eA.hom).mp
  simp only [modelFactorizationMap, Category.assoc, ← hp, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

theorem modelFactorizationMap_factors {P P' : C} (eP : P' ≅ P)
    (h : X ⟶ Z) (j : Z ⟶ P) (i : X ⟶ P) (j' : Z' ⟶ P') (i' : X' ⟶ P')
    (hj : eZ.hom ≫ j = j' ≫ eP.hom) (hi : eX.hom ≫ i = i' ≫ eP.hom) (hh : h ≫ j = i) :
    modelFactorizationMap eX eZ h ≫ j' = i' := by
  rw [modelFactorizationMap_comp eX eZ eP h j j' hj, hh, ← Category.assoc, hi,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem modelFactorizationMap_projection_isIso (eA : A' ≅ A)
    (h : X ⟶ Z) (p : Z ⟶ A) (p' : Z' ⟶ A') (hp : eZ.hom ≫ p = p' ≫ eA.hom)
    [IsIso (h ≫ p)] : IsIso (modelFactorizationMap eX eZ h ≫ p') := by
  rw [modelFactorizationMap_comp eX eZ eA h p p' hp]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InverseModelFactorization
