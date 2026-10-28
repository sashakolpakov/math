import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Differentials
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.EvaluationNaturality

/-! # Faces -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Faces

noncomputable section

/-! Each native prism face is evaluation on the corresponding deleted
tuple, restricted to the common intersection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite

universe u v w t
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{t} A]
  {ι : Type t} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ A) (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))

open OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.IntrinsicComponents.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.EvaluationNaturality

theorem evaluation (m n : ℕ) (a : Fin (m + 1) → ι) (b : Fin (n + 1) → ι) :
    IntrinsicComponents.Intrinsic.map U Q B γ h m n ≫ IntrinsicComponents.Intrinsic.projection U B m n a b =
      EvaluationNaturality.value U Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) (m + n + 1)
        (List.ofFn a ++ List.ofFn b) := by
  rw [IntrinsicComponents.Intrinsic.map_projection, Evaluation.Components.component_evaluation]
  rfl

theorem inner_face (m n : ℕ) (a : Fin (m + 2) → ι) (b : Fin (n + 1) → ι)
    (i : Fin (m + 2)) :
    IntrinsicComponents.Intrinsic.map U Q B γ h m n ≫ IntrinsicComponents.Intrinsic.projection U B m n (a ∘ i.succAbove) b ≫
        (B.obj (op (∏ᶜ (U ∘ b)))).map
          (NonemptyCechDifferential.faceMap U m i a).op =
      EvaluationNaturality.value U Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) (m + n + 1)
        (List.ofFn (a ∘ i.succAbove) ++ List.ofFn b) := by
  rw [← Category.assoc, evaluation, ← Evaluation.Components.ofFn_tuple]
  exact EvaluationNaturality.inner U Q B γ h
    (Cech.LocalTupleEvaluation.delete_le U m a i) (m + n + 1)
    (Components.tuple (a ∘ i.succAbove) b)
    (Components.product_tuple U (a ∘ i.succAbove) b).ge

theorem outer_face (m n : ℕ) (a : Fin (m + 1) → ι) (b : Fin (n + 2) → ι)
    (i : Fin (n + 2)) :
    IntrinsicComponents.Intrinsic.map U Q B γ h m n ≫ IntrinsicComponents.Intrinsic.projection U B m n a (b ∘ i.succAbove) ≫
        (B.map (NonemptyCechDifferential.faceMap U n i b).op).app
          (op (∏ᶜ (U ∘ a))) =
      EvaluationNaturality.value U Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) (m + n + 1)
        (List.ofFn a ++ List.ofFn (b ∘ i.succAbove)) := by
  rw [← Category.assoc, evaluation, ← Evaluation.Components.ofFn_tuple]
  exact EvaluationNaturality.outer U Q B γ h
    (Cech.LocalTupleEvaluation.delete_le U n b i) (m + n + 1)
    (Components.tuple a (b ∘ i.succAbove))
    (Components.product_tuple U a (b ∘ i.succAbove)).ge

omit [HasProducts.{t} A] [Finite ι] in
private theorem boundary_comp {X Y Z : A} (f : List ι → (X ⟶ Y)) (g : Y ⟶ Z)
    (l : List ι) :
    Cech.TupleConcatenation.boundaryValue (fun a => f a ≫ g) l =
      Cech.TupleConcatenation.boundaryValue f l ≫ g := by
  simp only [Cech.TupleConcatenation.boundaryValue, sum_comp, zsmul_comp]

theorem source (m n : ℕ) (a : Fin (m + 1) → ι) (b : Fin (n + 1) → ι) :
    ((NonemptyCechNerve.complexFunctor U).obj Q).d (m + n) (m + n + 1) ≫
        IntrinsicComponents.Intrinsic.map U Q B γ h m n ≫ IntrinsicComponents.Intrinsic.projection U B m n a b =
      Cech.TupleConcatenation.boundaryValue
        (EvaluationNaturality.value U Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) (m + n))
        (List.ofFn a ++ List.ofFn b) := by
  rw [evaluation, ← Evaluation.Components.ofFn_tuple]
  change _ = Cech.TupleConcatenation.boundaryValue
    (fun l => Cech.LocalTupleEvaluation.value U Q
      ((∏ᶜ (U ∘ a)) ⊓ (∏ᶜ (U ∘ b))) (m + n) l ≫
        SemilatticeCechAmalgamation.map Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b))) _
  dsimp only [EvaluationNaturality.value]
  rw [boundary_comp, Cech.LocalTupleEvaluation.boundary U Q _ (m + n)
    (Components.tuple a b) (Components.product_tuple U a b).ge,
    Cech.LocalTupleEvaluation.value_ofFn U Q _ (Components.tuple a b)
      (Components.product_tuple U a b).ge]
  simp only [Category.assoc]

theorem inner (m n : ℕ) (a : Fin (m + 2) → ι) (b : Fin (n + 1) → ι) :
    IntrinsicComponents.Intrinsic.map U Q B γ h m n ≫ ((IntrinsicComponents.Intrinsic.complex U B).d m (m + 1)).f n ≫
        IntrinsicComponents.Intrinsic.projection U B (m + 1) n a b =
      Cech.FiniteTupleConcatenation.boundaryValue
        (fun l => EvaluationNaturality.value U Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b))
          (m + n + 1) (l ++ List.ofFn b)) a := by
  rw [Differentials.inner, comp_sum]
  unfold Cech.FiniteTupleConcatenation.boundaryValue
  apply Finset.sum_congr rfl
  intro i _
  rw [comp_zsmul, inner_face]

theorem outer (m n : ℕ) (a : Fin (m + 1) → ι) (b : Fin (n + 2) → ι) :
    IntrinsicComponents.Intrinsic.map U Q B γ h m n ≫ ((IntrinsicComponents.Intrinsic.complex U B).X m).d n (n + 1) ≫
        IntrinsicComponents.Intrinsic.projection U B m (n + 1) a b =
      Cech.FiniteTupleConcatenation.boundaryValue
        (fun l => EvaluationNaturality.value U Q B γ h (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b))
          (m + n + 1) (List.ofFn a ++ l)) b := by
  rw [Differentials.outer, comp_sum]
  unfold Cech.FiniteTupleConcatenation.boundaryValue
  apply Finset.sum_congr rfl
  intro i _
  rw [comp_zsmul, outer_face]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Faces
