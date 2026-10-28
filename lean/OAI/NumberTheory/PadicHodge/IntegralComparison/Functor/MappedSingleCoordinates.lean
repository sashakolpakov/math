import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleMapCoordinates

/-! # Mapped Single Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.MappedSingleCoordinates

noncomputable section

/-! Mapping a single coefficient through an additive functor preserves
its original single-total coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z r s
variable {C : Type u} [Category.{v} C] [Abelian C]
  {C' : Type w} [Category.{z} C'] [Abelian C']
  {D : Type r} [Category.{s} D] [Abelian D] [HasCoproducts.{0} D]
  (H : C ⥤ C') [H.Additive] (F : C' ⥤ CochainComplex D ℕ) [F.Additive]
  (M : C) (c : ℕ)

def map : SingleTotal.bicomplex (H ⋙ F) M c ⟶ SingleTotal.bicomplex F (H.obj M) c :=
  (F.mapHomologicalComplex (.up ℕ)).map ((singleMapHomologicalComplex H (.up ℕ) c).hom.app M)

omit [HasCoproducts D] in
theorem row : (MappedSingleCoordinates.map H F M c).f c ≫ (SingleTotal.rowIso F (H.obj M) c).hom =
    (SingleTotal.rowIso (H ⋙ F) M c).hom := by
  change F.map (((singleMapHomologicalComplex H (.up ℕ) c).hom.app M).f c) ≫
    F.map (singleObjXSelf (.up ℕ) c (H.obj M)).hom = _
  rw [← F.map_comp, singleMapHomologicalComplex_hom_app_self]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem comparison (n : ℕ) :
    homologyMap (HomologicalComplex₂.total.map (MappedSingleCoordinates.map H F M c) (.up ℕ)) (n+c) ≫
      (SingleTotal.homologyIso F (H.obj M) c n).hom = (SingleTotal.homologyIso (H ⋙ F) M c n).hom := by
  have h := SingleMapCoordinates.comparison (H ⋙ F) F M (H.obj M) c
    (MappedSingleCoordinates.map H F M c) (𝟙 _) (by simpa only [Category.comp_id] using row H F M c) n
  simpa only [homologyMap_id, Category.comp_id] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.MappedSingleCoordinates
