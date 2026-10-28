import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockGroupComparison

/-! # Iterated Base Change Naturality -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IteratedBaseChangeNaturality

noncomputable section

/-! The actual iterated pullback comparisons commute with every source
morphism, so they retain the inclusions of the original kernel blocks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S T U : Scheme} {A B : Over S}
  (f : T ⟶ S) (h : U ⟶ T) (g : U ⟶ S) (w : h ≫ f = g) (a : A ⟶ B)

theorem iteratedIso_natural :
    (PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso A f h g w).hom ≫ (Over.pullback g).map a =
      (Over.pullback h).map ((Over.pullback f).map a) ≫ (PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso B f h g w).hom := by
  subst g
  change ((PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.compositeIso A f h).inv ≫ PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.congrMap A (h ≫ f) (h ≫ f) rfl) ≫
      (Over.pullback (h ≫ f)).map a =
    (Over.pullback h).map ((Over.pullback f).map a) ≫
      ((PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.compositeIso B f h).inv ≫ PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.congrMap B (h ≫ f) (h ≫ f) rfl)
  rw [PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.congrMap_self, PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.congrMap_self, Category.comp_id, Category.comp_id]
  exact ((Over.pullbackComp h f).inv.naturality a).symm

theorem iso_comparison_natural {C : Type*} [Category C]
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
    (e₁ : X₁ ≅ Z₁) (e₂ : X₂ ≅ Z₂) (d₁ : Y₁ ≅ Z₁) (d₂ : Y₂ ≅ Z₂)
    (x : X₁ ⟶ X₂) (y : Y₁ ⟶ Y₂) (z : Z₁ ⟶ Z₂)
    (he : e₁.hom ≫ z = x ≫ e₂.hom) (hd : d₁.hom ≫ z = y ≫ d₂.hom) :
    (e₁ ≪≫ d₁.symm).hom ≫ y = x ≫ (e₂ ≪≫ d₂.symm).hom := by
  apply (cancel_mono d₂.hom).mp
  change ((e₁.hom ≫ d₁.inv) ≫ y) ≫ d₂.hom =
    (x ≫ (e₂.hom ≫ d₂.inv)) ≫ d₂.hom
  rw [Category.assoc, Category.assoc, ← hd, Iso.inv_hom_id_assoc,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact he

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IteratedBaseChangeNaturality
