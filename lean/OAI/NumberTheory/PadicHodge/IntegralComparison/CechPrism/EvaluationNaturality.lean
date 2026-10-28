import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Evaluation

/-! # Evaluation Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.EvaluationNaturality

noncomputable section

/-! Restricting either intersection in a prism component is the
literal restriction of its common-intersection evaluation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w t
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Preadditive A] [HasProducts.{t} A]
  {ι : Type t} (U : ι → C)
  (Q : Cᵒᵖ ⥤ A) (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))

def value (I V : C) (r : ℕ) (l : List ι) :=
  Cech.LocalTupleEvaluation.value U Q (I ⊓ V) r l ≫
    SemilatticeCechAmalgamation.map Q B γ h I V

theorem naturality {I I' V V' : C} (hi : I' ≤ I) (hv : V' ≤ V)
    (r : ℕ) (a : Fin (r + 1) → ι) (ha : I ⊓ V ≤ ∏ᶜ (U ∘ a)) :
    value U Q B γ h I V r (List.ofFn a) ≫
        (B.obj (op V)).map (homOfLE hi).op ≫
          (B.map (homOfLE hv).op).app (op I') =
      value U Q B γ h I' V' r (List.ofFn a) := by
  dsimp only [value]
  rw [Category.assoc, SemilatticeCechAmalgamation.naturality,
    ← Category.assoc, Cech.LocalTupleEvaluation.value_restrict U Q (inf_le_inf hi hv) a ha]

theorem inner {I I' V : C} (hi : I' ≤ I)
    (r : ℕ) (a : Fin (r + 1) → ι) (ha : I ⊓ V ≤ ∏ᶜ (U ∘ a)) :
    value U Q B γ h I V r (List.ofFn a) ≫ (B.obj (op V)).map (homOfLE hi).op =
      value U Q B γ h I' V r (List.ofFn a) := by
  have hn := naturality U Q B γ h hi (le_refl V) r a ha
  simpa only [homOfLE_refl, op_id, B.map_id, NatTrans.id_app, Category.comp_id] using hn

theorem outer {I V V' : C} (hv : V' ≤ V)
    (r : ℕ) (a : Fin (r + 1) → ι) (ha : I ⊓ V ≤ ∏ᶜ (U ∘ a)) :
    value U Q B γ h I V r (List.ofFn a) ≫ (B.map (homOfLE hv).op).app (op I) =
      value U Q B γ h I V' r (List.ofFn a) := by
  have hn := naturality U Q B γ h (le_refl I) hv r a ha
  simpa only [homOfLE_refl, op_id, (B.obj (op V)).map_id, Category.id_comp] using hn

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.EvaluationNaturality
