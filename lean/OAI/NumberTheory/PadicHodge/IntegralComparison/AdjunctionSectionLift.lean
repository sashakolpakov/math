import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Adjunction Section Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AdjunctionSectionLift

noncomputable section

/-! An adjunction with invertible unit lifts a map of sections back to
the original objects when the source counit is invertible. -/

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
  {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [IsIso a.unit]
  (M N : D) [IsIso (a.counit.app M)] (t : G.obj M ⟶ G.obj N)

def lift : M ⟶ N := inv (a.counit.app M) ≫ F.map t ≫ a.counit.app N

theorem map_lift : G.map (lift a M N t) = t := by
  have hc (P : D) : G.map (a.counit.app P) = inv (a.unit.app (G.obj P)) := by
    apply (cancel_epi (a.unit.app (G.obj P))).mp
    rw [IsIso.hom_inv_id]
    exact a.right_triangle_components P
  have hi : G.map (inv (a.counit.app M)) = a.unit.app (G.obj M) := by
    apply (cancel_mono (G.map (a.counit.app M))).mp
    rw [← G.map_comp, IsIso.inv_hom_id, G.map_id, hc, IsIso.hom_inv_id]
  simp only [lift, G.map_comp, hi, hc]
  have hn := a.unit.naturality t
  change t ≫ a.unit.app (G.obj N) = a.unit.app (G.obj M) ≫ G.map (F.map t) at hn
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AdjunctionSectionLift
