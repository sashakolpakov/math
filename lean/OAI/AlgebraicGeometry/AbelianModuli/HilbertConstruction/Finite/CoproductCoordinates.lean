import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoproductSections

/-! # Coproduct Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoproductCoordinates

noncomputable section

/-! Coordinates of finite coproducts and evaluation of their desc maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive
universe u v w z

def finiteCoproductProjection {C : Type v} [Category.{w} C] [Preadditive C]
    {ι : Type z} [Fintype ι] (M : ι → C) [HasCoproduct M] [HasBiproduct M]
    (i : ι) : (∐ M) ⟶ M i :=
  (biproduct.isoCoproduct M).inv ≫ biproduct.π M i

theorem finiteCoproduct_inclusion_eq {C : Type v} [Category.{w} C] [Preadditive C]
    {ι : Type z} [Fintype ι] (M : ι → C) [HasCoproduct M] [HasBiproduct M] (i : ι) :
    Sigma.ι M i = biproduct.ι M i ≫ (biproduct.isoCoproduct M).hom := by
  rw [biproduct.isoCoproduct_hom, biproduct.ι_desc]

theorem finiteCoproduct_total {C : Type v} [Category.{w} C] [Preadditive C]
    {ι : Type z} [Fintype ι] (M : ι → C) [HasCoproduct M] [HasBiproduct M] :
    ∑ i, finiteCoproductProjection M i ≫ Sigma.ι M i = 𝟙 (∐ M) := by
  simp_rw [finiteCoproductProjection, finiteCoproduct_inclusion_eq, Category.assoc]
  rw [← comp_sum]
  simp_rw [← Category.assoc]
  rw [← sum_comp]
  have ht : (∑ i, biproduct.π M i ≫ biproduct.ι M i) = 𝟙 (⨁ M) := IsBilimit.total (biproduct.isBilimit M)
  rw [ht]
  simpa only [Category.id_comp, Category.comp_id] using (biproduct.isoCoproduct M).inv_hom_id

theorem finiteCoproduct_desc_value {C : Type v} [Category.{w} C] [Preadditive C]
    {R : Type u} [CommRing R] (F : C ⥤ ModuleCat.{u} R) [F.Additive]
    {ι : Type z} [Fintype ι] (M : ι → C) [HasCoproduct M] [HasBiproduct M]
    {N : C} (f : ∀ i, M i ⟶ N) (x : F.obj (∐ M)) :
    F.map (Sigma.desc f) x =
      ∑ i, F.map (f i) (F.map (finiteCoproductProjection M i) x) := by
  have h : ∑ i, finiteCoproductProjection M i ≫ f i = Sigma.desc f := by
    calc
      _ = ∑ i, (finiteCoproductProjection M i ≫ Sigma.ι M i) ≫ Sigma.desc f := by
        simp only [Category.assoc, Sigma.ι_comp_desc]
      _ = (∑ i, finiteCoproductProjection M i ≫ Sigma.ι M i) ≫ Sigma.desc f :=
        (sum_comp _ _ _).symm
      _ = Sigma.desc f := by rw [finiteCoproduct_total, Category.id_comp]
  rw [← h, F.map_sum]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply,
    CategoryTheory.Functor.map_comp, ModuleCat.comp_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoproductCoordinates
