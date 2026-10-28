import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-! # Split Ext Vanishing -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.SplitExtVanishing.FiniteSplitExtVanishing

noncomputable section

/-! # Ext vanishing under target isomorphisms and finite coefficient splittings -/

open _root_.CategoryTheory

universe u v e

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{e} C]

theorem of_targetIso {X Y Y' : C} (i : Y ≅ Y') (n : ℕ)
    (h : ∀ α : Abelian.Ext X Y' n, α = 0) (α : Abelian.Ext X Y n) : α = 0 := by
  have hz := congrArg (fun β : Abelian.Ext X Y' n => β.comp (Abelian.Ext.mk₀ i.inv) (add_zero n))
    (h (α.comp (Abelian.Ext.mk₀ i.hom) (add_zero n)))
  simpa only [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    i.hom_inv_id, Abelian.Ext.comp_mk₀_id, Abelian.Ext.zero_comp] using hz

theorem of_splitting {X Y : C} {ι : Type*} [Fintype ι] (Z : ι → C)
    (π : ∀ i, Y ⟶ Z i) (ι' : ∀ i, Z i ⟶ Y) (hπ : ∑ i, π i ≫ ι' i = 𝟙 Y)
    (n : ℕ) (h : ∀ i (α : Abelian.Ext X (Z i) n), α = 0)
    (α : Abelian.Ext X Y n) : α = 0 := by
  calc
    α = α.comp (Abelian.Ext.mk₀ (∑ i, π i ≫ ι' i)) (add_zero n) := by
      rw [hπ, Abelian.Ext.comp_mk₀_id]
    _ = ∑ i, (α.comp (Abelian.Ext.mk₀ (π i)) (add_zero n)).comp
        (Abelian.Ext.mk₀ (ι' i)) (add_zero n) := by
      simp only [Abelian.Ext.mk₀_sum, Abelian.Ext.comp_sum,
        Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
    _ = 0 := by simp only [h, Abelian.Ext.zero_comp, Finset.sum_const_zero]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.SplitExtVanishing.FiniteSplitExtVanishing
