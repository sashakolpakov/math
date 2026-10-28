import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.BigOperators.Fin

/-! # Retract Copies -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.RetractCopies

noncomputable section

/-! A finite matrix identity exhibiting an object as a retract of finitely
many copies of another object. It is stable under additive functors and biproducts. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive
open scoped BigOperators
variable {C D : Type*} [Category* C] [Preadditive C] [Category* D] [Preadditive D]

def FiniteRetractCopies (L M : C) : Prop :=
  ∃ (n : ℕ) (ι : Fin n → (L ⟶ M)) (π : Fin n → (M ⟶ L)), ∑ i, π i ≫ ι i = 𝟙 M

namespace FiniteRetractCopies

theorem self (L : C) : FiniteRetractCopies L L :=
  ⟨1, fun _ => 𝟙 L, fun _ => 𝟙 L, by simp⟩

theorem of_isZero (L M : C) (hM : IsZero M) : FiniteRetractCopies L M :=
  ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, by simp [hM.eq_of_src (𝟙 M) 0]⟩

theorem of_targetIso {L M N : C} (h : FiniteRetractCopies L M) (e : M ≅ N) :
    FiniteRetractCopies L N := by
  obtain ⟨n, ι, π, he⟩ := h
  refine ⟨n, fun i => ι i ≫ e.hom, fun i => e.inv ≫ π i, ?_⟩
  calc
    _ = e.inv ≫ (∑ i, π i ≫ ι i) ≫ e.hom := by simp only [comp_sum, sum_comp, Category.assoc]
    _ = 𝟙 N := by rw [he]; simp

theorem of_sourceIso {L L' M : C} (h : FiniteRetractCopies L M) (e : L ≅ L') :
    FiniteRetractCopies L' M := by
  obtain ⟨n, ι, π, he⟩ := h
  refine ⟨n, fun i => e.inv ≫ ι i, fun i => π i ≫ e.hom, ?_⟩
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using he

theorem map {L M : C} (h : FiniteRetractCopies L M) (F : C ⥤ D) [F.Additive] :
    FiniteRetractCopies (F.obj L) (F.obj M) := by
  obtain ⟨n, ι, π, he⟩ := h
  refine ⟨n, fun i => F.map (ι i), fun i => F.map (π i), ?_⟩
  have h := congrArg F.map he
  simpa only [F.map_sum, F.map_comp, F.map_id] using h

theorem biprod [HasBinaryBiproducts C] {L M N : C}
    (hM : FiniteRetractCopies L M) (hN : FiniteRetractCopies L N) :
    FiniteRetractCopies L (M ⊞ N) := by
  obtain ⟨m, ιM, πM, heM⟩ := hM
  obtain ⟨n, ιN, πN, heN⟩ := hN
  let ι : Fin (m + n) → (L ⟶ M ⊞ N) :=
    Fin.addCases (fun i => ιM i ≫ biprod.inl) (fun i => ιN i ≫ biprod.inr)
  let π : Fin (m + n) → (M ⊞ N ⟶ L) :=
    Fin.addCases (fun i => biprod.fst ≫ πM i) (fun i => biprod.snd ≫ πN i)
  refine ⟨m + n, ι, π, ?_⟩
  calc
    _ = (∑ i, biprod.fst ≫ (πM i ≫ ιM i) ≫ biprod.inl) +
        (∑ i, biprod.snd ≫ (πN i ≫ ιN i) ≫ biprod.inr) := by
      rw [Fin.sum_univ_add]
      simp only [π, ι, Fin.addCases_left, Fin.addCases_right, Category.assoc]
    _ = biprod.fst ≫ (∑ i, πM i ≫ ιM i) ≫ biprod.inl +
        biprod.snd ≫ (∑ i, πN i ≫ ιN i) ≫ biprod.inr := by
      simp only [comp_sum, sum_comp, Category.assoc]
    _ = 𝟙 (M ⊞ N) := by rw [heM, heN]; simp only [Category.id_comp, biprod.total]

end FiniteRetractCopies

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.RetractCopies
