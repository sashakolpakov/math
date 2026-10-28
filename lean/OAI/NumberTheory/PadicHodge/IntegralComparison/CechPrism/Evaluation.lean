import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Components
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.LocalTupleEvaluation

/-! # Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Evaluation.Components

noncomputable section

/-! The original concatenation-prism component is evaluation on its
concatenated tuple followed by the actual inverse-meet map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w t
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Preadditive A] [HasProducts.{t} A]
  {ι : Type t} (U : ι → C)
  (Q : Cᵒᵖ ⥤ A) (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))

theorem ofFn_tuple {m n : ℕ} (a : Fin (m + 1) → ι) (b : Fin (n + 1) → ι) :
    List.ofFn (Components.tuple a b) = List.ofFn a ++ List.ofFn b := by
  exact (List.ofFn_congr (by omega : (m + 1) + (n + 1) = m + n + 1 + 1)
    (Fin.append a b)).symm.trans (List.ofFn_fin_append a b)

theorem component_evaluation (m n : ℕ) (a : Fin (m + 1) → ι) (b : Fin (n + 1) → ι) :
    Components.component U Q B γ h m n a b =
      Cech.LocalTupleEvaluation.value U Q ((∏ᶜ (U ∘ a)) ⊓ (∏ᶜ (U ∘ b)))
        (m + n + 1) (List.ofFn a ++ List.ofFn b) ≫
          SemilatticeCechAmalgamation.map Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) := by
  rw [← ofFn_tuple]
  have ht : (∏ᶜ (U ∘ a)) ⊓ (∏ᶜ (U ∘ b)) ≤ ∏ᶜ (U ∘ Components.tuple a b) :=
    (Components.product_tuple U a b).ge
  rw [Cech.LocalTupleEvaluation.value_ofFn U Q _ (Components.tuple a b) ht]
  dsimp only [Components.component]
  rw [Category.assoc]
  congr 2

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Evaluation.Components
