import Mathlib.Algebra.Homology.Additive

/-! # Single Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleCoordinates

noncomputable section

/-! A map into a single complex retains its literal surviving
component after applying an additive functor and changing coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

universe u v w z
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {D : Type w} [Category.{z} D] [Preadditive D] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ) (N : C) (n : ℕ)
  (a : K ⟶ (single C (.up ℕ) n).obj N)

def map : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶
    (single D (.up ℕ) n).obj (F.obj N) :=
  (F.mapHomologicalComplex (.up ℕ)).map a ≫
    (singleMapHomologicalComplex F (.up ℕ) n).hom.app N

theorem top : (SingleCoordinates.map F K N n a).f n ≫ (singleObjXSelf (.up ℕ) n (F.obj N)).hom =
    F.map (a.f n ≫ (singleObjXSelf (.up ℕ) n N).hom) := by
  dsimp only [SingleCoordinates.map]
  rw [HomologicalComplex.comp_f, singleMapHomologicalComplex_hom_app_self]
  change (F.map (a.f n) ≫
    (F.map (singleObjXSelf (.up ℕ) n N).hom ≫ (singleObjXSelf (.up ℕ) n (F.obj N)).inv)) ≫
    (singleObjXSelf (.up ℕ) n (F.obj N)).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp]

variable {L : CochainComplex D ℕ} (b : L ⟶ (F.mapHomologicalComplex (.up ℕ)).obj K)
  {P : D} (e : F.obj N ⟶ P)

theorem compose_top :
    ((b ≫ SingleCoordinates.map F K N n a ≫ (single D (.up ℕ) n).map e).f n) ≫
        (singleObjXSelf (.up ℕ) n P).hom =
      b.f n ≫ F.map (a.f n ≫ (singleObjXSelf (.up ℕ) n N).hom) ≫ e := by
  simp only [HomologicalComplex.comp_f, single_map_f_self, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc ((SingleCoordinates.map F K N n a).f n), top]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleCoordinates
