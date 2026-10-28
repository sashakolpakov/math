import OAI.AlgebraicGeometry.ComplexMultiplication.ExtSmallComparison

/-! # Shifted Derived Augmentation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ShiftedDerivedAugmentation

noncomputable section

/-! # Cancelling genuine source and target isomorphisms before augmentation -/

open _root_.CategoryTheory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

theorem shiftedDerivedAugmentation_normalization
    {A B A' B' I : CochainComplex C ℤ} (eA : A ≅ A') (eB : B ≅ B')
    (f : B ⟶ I) (n : ℤ)
    (a : ShiftedHom (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B) n) :
    DerivedCategory.Q.map eA.hom ≫
      (DerivedCategory.Q.map eA.inv ≫ a ≫ (DerivedCategory.Q.map eB.hom)⟦n⟧') ≫
        (DerivedCategory.Q.map (eB.inv ≫ f))⟦n⟧' =
      a ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, eA.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have hb : DerivedCategory.Q.map eB.hom ≫ DerivedCategory.Q.map eB.inv =
      𝟙 (DerivedCategory.Q.obj B) := by
    rw [← CategoryTheory.Functor.map_comp, eB.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [← (shiftFunctor (DerivedCategory C) n).map_comp_assoc, hb,
    CategoryTheory.Functor.map_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ShiftedDerivedAugmentation
