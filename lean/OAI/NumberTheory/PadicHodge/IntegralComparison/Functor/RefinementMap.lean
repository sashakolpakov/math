import Mathlib.CategoryTheory.Preadditive.Basic

/-! # Refinement Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.RefinementMap

noncomputable section

/-! The actual right map followed by inverse left map is natural under
any comparison of functors that inverts those original left maps. -/
open _root_.CategoryTheory
universe u v w z
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  (F G : C ⥤ D) (τ : F ⟶ G)
  {P K T : C} (l : K ⟶ T) (r : P ⟶ T)
  [IsIso (F.map l)] [IsIso (G.map l)]

def map : F.obj P ⟶ F.obj K := F.map r ≫ inv (F.map l)

@[reassoc]
theorem map_left : RefinementMap.map F l r ≫ F.map l = F.map r := by
  simp only [RefinementMap.map, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

@[reassoc]
theorem naturality : RefinementMap.map F l r ≫ τ.app K = τ.app P ≫ RefinementMap.map G l r := by
  apply (cancel_mono (G.map l)).mp
  simp only [Category.assoc]
  rw [← τ.naturality l, ← Category.assoc (RefinementMap.map F l r), map_left, τ.naturality r]
  simp only [RefinementMap.map, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.RefinementMap
