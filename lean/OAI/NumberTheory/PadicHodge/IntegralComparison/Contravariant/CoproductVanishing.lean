import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoproductVanishing
import Mathlib.CategoryTheory.Preadditive.Opposite

/-! # Coproduct Vanishing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.CoproductVanishing

noncomputable section

/-! Vanishing for additive contravariant functors on finite coproducts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {R : Type w} [Ring R] (F : Cᵒᵖ ⥤ ModuleCat.{w} R) [F.Additive]

theorem isZero_image {I : Type} [Fintype I] (M : I → C)
    (hM : ∀ i, IsZero (F.obj (op (M i)))) : IsZero (F.obj (op (∐ M))) := by
  classical
  have hz : IsZero (F.obj (op (⨁ M))) := by
    rw [IsZero.iff_id_eq_zero, ← F.map_id]
    have hid : 𝟙 (op (⨁ M)) =
        ∑ i, (biproduct.ι M i).op ≫ (biproduct.π M i).op := by
      rw [← op_id, ← biproduct.total]
      simp only [op_sum, op_comp]
    rw [hid, F.map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [F.map_comp, (hM i).eq_zero_of_tgt (F.map (biproduct.ι M i).op), zero_comp]
  exact hz.of_iso (F.mapIso (biproduct.isoCoproduct M).op)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.CoproductVanishing
