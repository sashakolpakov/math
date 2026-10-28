import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Coproduct Vanishing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoproductVanishing

noncomputable section

/-! An additive functor carries a finite coproduct of objects with vanishing
images to a zero object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {R : Type w} [Ring R] (F : C ⥤ ModuleCat.{w} R) [F.Additive]

theorem isZero_image {I : Type} [Fintype I] (M : I → C)
    (hM : ∀ i, IsZero (F.obj (M i))) : IsZero (F.obj (∐ M)) := by
  classical
  let : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  let e₀ : F.obj (∐ M) ≅ F.obj (⨁ M) := F.mapIso (biproduct.isoCoproduct M).symm
  let e₁ : F.obj (⨁ M) ≅ ⨁ (F.obj ∘ M) := F.mapBiproduct M
  have hz : IsZero (⨁ (F.obj ∘ M)) := by
    rw [IsZero.iff_id_eq_zero]
    apply biproduct.hom_ext
    intro i
    exact (hM i).eq_of_tgt _ _
  exact hz.of_iso (e₀ ≪≫ e₁)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoproductVanishing
