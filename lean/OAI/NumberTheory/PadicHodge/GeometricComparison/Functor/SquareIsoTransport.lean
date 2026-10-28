import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Iso

/-! # Square Iso Transport -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.SquareIsoTransport.FunctorSquareIsoTransport

/-! A natural square of functors respects transport through source and
target isomorphisms. -/

open _root_.CategoryTheory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  (T : C ⥤ D) (S : C ⥤ E) (S' : D ⥤ E) (b : S ⟶ T ⋙ S')
  {K K' : C} {L L' : D} (e : K ≅ K') (d : L ≅ L') (a : T.obj K' ⟶ L')

theorem square : S.map e.inv ≫ (b.app K ≫ S'.map (T.map e.hom ≫ a ≫ d.inv)) =
    (b.app K' ≫ S'.map a) ≫ S'.map d.inv := by
  rw [← Category.assoc, b.naturality]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [← Category.assoc (S'.map (T.map e.inv)), ← S'.map_comp, ← T.map_comp,
    e.inv_hom_id, T.map_id, S'.map_id, Category.id_comp]

end OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.SquareIsoTransport.FunctorSquareIsoTransport
