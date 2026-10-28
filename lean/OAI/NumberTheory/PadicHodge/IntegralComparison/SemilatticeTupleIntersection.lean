import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.CechAugmentation
import Mathlib.Data.Fin.Tuple.Basic

/-! # Semilattice Tuple Intersection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SemilatticeTupleIntersection

noncomputable section

/-! Products of the actual Čech tuples are their intersections;
concatenating tuples gives the meet of the two tuple products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [SemilatticeInf C]

theorem le_product {ι : Type v} (F : ι → C) [HasProduct F] (T : C) :
    T ≤ ∏ᶜ F ↔ ∀ i, T ≤ F i := by
  constructor
  · intro h i
    exact leOfHom (homOfLE h ≫ Pi.π F i)
  · intro h
    exact leOfHom (Pi.lift (fun i => homOfLE (h i)))

theorem product_le {ι : Type v} (F : ι → C) [HasProduct F] (i : ι) :
    (∏ᶜ F) ≤ F i := leOfHom (Pi.π F i)

theorem product_reindex {ι κ : Type v} (F : ι → C) (e : κ ≃ ι)
    [HasProduct F] [HasProduct (F ∘ e)] :
    (∏ᶜ (F ∘ e)) = ∏ᶜ F := by
  apply le_antisymm
  · apply (le_product F _).mpr
    intro i
    simpa only [Function.comp_apply, e.apply_symm_apply] using product_le (F ∘ e) (e.symm i)
  · apply (le_product (F ∘ e) _).mpr
    intro i
    exact product_le F (e i)

theorem product_append {m n : ℕ} (a : Fin (m + 1) → C) (b : Fin (n + 1) → C) :
    (∏ᶜ Fin.append a b) = (∏ᶜ a) ⊓ (∏ᶜ b) := by
  apply le_antisymm
  · apply le_inf
    · apply (le_product a _).mpr
      intro i
      simpa only [Fin.append_left] using product_le (Fin.append a b) (i.castAdd (n + 1))
    · apply (le_product b _).mpr
      intro i
      simpa only [Fin.append_right] using product_le (Fin.append a b) (i.natAdd (m + 1))
  · apply (le_product (Fin.append a b) _).mpr
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using inf_le_left.trans (product_le a j)
    · simpa only [Fin.append_right] using inf_le_right.trans (product_le b j)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SemilatticeTupleIntersection
