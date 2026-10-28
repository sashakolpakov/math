import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleHomology

/-! # Single Composite Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleCompositeHomology

noncomputable section

/-! Homology coordinates for an evaluated map to a single complex,
including the original source comparison and target normalization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  (K : CochainComplex C ℕ) (N : C) (n : ℕ)
  (a : K ⟶ (single C (.up ℕ) n).obj N)
  (L : CochainComplex D ℕ) (b : L ⟶ (F.mapHomologicalComplex (.up ℕ)).obj K)
  (P : D) (e : F.obj N ⟶ P)

theorem homology :
    homologyMap (b ≫ SingleCoordinates.map F K N n a ≫
      (single D (.up ℕ) n).map e) n ≫ (singleObjHomologySelfIso (.up ℕ) n P).hom =
      homologyMap b n ≫ ((K.sc n).mapHomologyIso F).hom ≫
        F.map (homologyMap a n ≫ (singleObjHomologySelfIso (.up ℕ) n N).hom) ≫ e := by
  simp only [homologyMap_comp, Category.assoc, singleObjHomologySelfIso_hom_naturality]
  rw [← Category.assoc (homologyMap (SingleCoordinates.map F K N n a) n),
    SingleHomology.map]
  simp only [Category.assoc]

theorem homology_expanded :
    homologyMap (b ≫ (F.mapHomologicalComplex (.up ℕ)).map a ≫
      (singleMapHomologicalComplex F (.up ℕ) n).hom.app N ≫
      (single D (.up ℕ) n).map e) n ≫ (singleObjHomologySelfIso (.up ℕ) n P).hom =
      homologyMap b n ≫ ((K.sc n).mapHomologyIso F).hom ≫
        F.map (homologyMap a n ≫ (singleObjHomologySelfIso (.up ℕ) n N).hom) ≫ e := by
  simpa only [SingleCoordinates.map, Category.assoc] using
    homology F K N n a L b P e

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleCompositeHomology
