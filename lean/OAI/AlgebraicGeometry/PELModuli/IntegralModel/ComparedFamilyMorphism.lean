import Mathlib.CategoryTheory.Iso

/-! # Compared Family Morphism -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComparedFamilyMorphism

noncomputable section

/-! A commuting morphism comparison retains its equation when both
source conventions are changed through a natural isomorphism. -/

open _root_.CategoryTheory

theorem compared_family_morphism {C : Type*} [Category* C]
    {G H G' H' A D : C} (cA : G ≅ G') (cD : H ≅ H') (eA : G ≅ A) (eD : H ≅ D)
    (m : G ⟶ H) (m' : G' ⟶ H') (f : A ⟶ D)
    (hc : m ≫ cD.hom = cA.hom ≫ m') (he : eA.hom ≫ f = m ≫ eD.hom) :
    (cA.symm ≪≫ eA).hom ≫ f = m' ≫ (cD.symm ≪≫ eD).hom := by
  change (cA.inv ≫ eA.hom) ≫ f = m' ≫ (cD.inv ≫ eD.hom)
  apply (cancel_epi cA.hom).mp
  simp only [Category.assoc, cA.hom_inv_id_assoc]
  rw [← Category.assoc cA.hom, ← hc, Category.assoc, cD.hom_inv_id_assoc]
  exact he

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComparedFamilyMorphism
