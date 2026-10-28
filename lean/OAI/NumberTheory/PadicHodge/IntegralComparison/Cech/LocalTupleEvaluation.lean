import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.FiniteTupleConcatenation
import OAI.NumberTheory.PadicHodge.IntegralComparison.SemilatticeTupleIntersection
import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechDifferential

/-! # Local Tuple Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.LocalTupleEvaluation

noncomputable section

/-! A homogeneous Čech cochain evaluated on supported finite lists.
This is a bookkeeping device for the genuine categorical projection
and restriction maps; its alternating list boundary is the original
Čech differential. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w t
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Preadditive A] [HasProducts.{t} A]
  {ι : Type t} (U : ι → C) (Q : Cᵒᵖ ⥤ A)

def tuple {n : ℕ} (l : List ι) (h : l.length = n + 1) : Fin (n + 1) → ι :=
  l.get ∘ Fin.cast h.symm

theorem tuple_ofFn {n : ℕ} (a : Fin (n + 1) → ι) :
    tuple (List.ofFn a) (List.length_ofFn (f := a)) = a := by
  funext i
  simp only [tuple, Function.comp_apply, List.get_ofFn]
  rfl

def supportedValue (T : C) (n : ℕ) (a : Fin (n + 1) → ι) :
    ((NonemptyCechNerve.complexFunctor U).obj Q).X n ⟶ Q.obj (op T) := by
  classical
  exact if hT : T ≤ ∏ᶜ (U ∘ a) then
      NonemptyCechDifferential.projection U Q n a ≫
        Q.map (homOfLE hT).op
  else 0

def value (T : C) (n : ℕ) (l : List ι) :
    ((NonemptyCechNerve.complexFunctor U).obj Q).X n ⟶ Q.obj (op T) := by
  classical
  exact if h : l.length = n + 1 then supportedValue U Q T n (tuple l h) else 0

theorem value_ofFn (T : C) {n : ℕ} (a : Fin (n + 1) → ι)
    (ha : T ≤ ∏ᶜ (U ∘ a)) :
    value U Q T n (List.ofFn a) =
      NonemptyCechDifferential.projection U Q n a ≫ Q.map (homOfLE ha).op := by
  classical
  unfold value
  rw [dite_eq_left (List.length_ofFn (f := a))]
  rw [tuple_ofFn]
  exact dite_eq_left ha

theorem value_restrict {T T' : C} (hT : T' ≤ T) {n : ℕ}
    (a : Fin (n + 1) → ι) (ha : T ≤ ∏ᶜ (U ∘ a)) :
    value U Q T n (List.ofFn a) ≫ Q.map (homOfLE hT).op =
      value U Q T' n (List.ofFn a) := by
  rw [value_ofFn U Q T a ha, value_ofFn U Q T' a (hT.trans ha),
    Category.assoc, ← Q.map_comp]
  congr 2

theorem delete_le (n : ℕ) (a : Fin (n + 2) → ι) (i : Fin (n + 2)) :
    (∏ᶜ (U ∘ a)) ≤ ∏ᶜ (U ∘ (a ∘ i.succAbove)) :=
  leOfHom (NonemptyCechDifferential.faceMap U n i a)

omit [HasProducts.{t} A] in
private theorem sum_comp {X Y Z : A} {n : ℕ} (f : Fin n → (X ⟶ Y))
    (a : Fin n → ℤ) (g : Y ⟶ Z) :
    (∑ i, a i • f i) ≫ g = ∑ i, a i • (f i ≫ g) := by
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]

theorem boundary (T : C) (n : ℕ) (a : Fin (n + 2) → ι)
    (ha : T ≤ ∏ᶜ (U ∘ a)) :
    TupleConcatenation.boundaryValue (value U Q T n) (List.ofFn a) =
      ((NonemptyCechNerve.complexFunctor U).obj Q).d n (n + 1) ≫
        NonemptyCechDifferential.projection U Q (n + 1) a ≫ Q.map (homOfLE ha).op := by
  rw [← FiniteTupleConcatenation.boundaryValue_eq]
  unfold FiniteTupleConcatenation.boundaryValue
  rw [← Category.assoc, NonemptyCechDifferential.differential_projection, LocalTupleEvaluation.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [value_ofFn U Q T (a ∘ i.succAbove) (ha.trans (delete_le U n a i))]
  rw [Category.assoc, ← Q.map_comp]
  congr 2

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.LocalTupleEvaluation
