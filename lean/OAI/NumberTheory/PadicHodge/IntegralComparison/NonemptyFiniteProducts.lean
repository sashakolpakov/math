import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-! # Nonempty Finite Products -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyFiniteProducts

noncomputable section

/-! Binary products suffice for all nonempty finite tuples in the original crystalline category. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]

theorem hasProduct : ∀ (n : ℕ) (f : Fin (n + 1) → C), HasProduct f
  | 0 => fun f => by
    let : Unique (Fin 1) :=
      { default := ⟨0, Nat.zero_lt_one⟩
        uniq i := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)) }
    exact HasLimit.mk (limitConeOfUnique f)
  | n + 1 => fun f => by
    let := hasProduct n (fun i => f i.succ)
    exact HasLimit.mk ⟨_, extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)⟩

instance hasProductsOfShape (n : ℕ) : HasProductsOfShape (Fin (n + 1)) C :=
  ⟨fun K => by
    let e : Discrete.functor (fun i => K.obj ⟨i⟩) ≅ K := Discrete.natIso (fun _ => Iso.refl _)
    rw [← hasLimit_iff_of_iso e]
    exact NonemptyFiniteProducts.hasProduct n _⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyFiniteProducts
