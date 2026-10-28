/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.SectionCechIndices
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-! # Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.Cech

noncomputable section

/-! The augmented ordered Čech complex of a finite family in a
preorder with finite products. Degree zero is evaluation on the empty
intersection, and degree q uses intersections of q distinct members.
This indexing retains the support degree without negative shifts. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite
universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)

def Index (ι : Type u) [Preorder ι] (n : ℕ) := {a : Fin n → ι // StrictMono a}

def Index.delete {n : ℕ} (a : Index ι (n + 1)) (k : Fin (n + 1)) : Index ι n :=
  ⟨a.val ∘ k.succAbove, a.property.comp (Fin.succAboveOrderEmb k).strictMono⟩

theorem Index.delete_delete {n : ℕ} (a : Index ι (n + 2))
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    (a.delete j.succ).delete i = (a.delete i.castSucc).delete j := by
  apply Subtype.ext
  funext k
  cases n with
  | zero => exact k.elim0
  | succ n =>
      have h := ConcreteCategory.congr_hom (SimplexCategory.δ_comp_δ hij)
      exact congrArg a.val (h k)

def formal (n : ℕ) : FormalCoproduct C where
  I := Index ι n
  obj a := ∏ᶜ fun i : Fin n => U (a.val i)

def face (n : ℕ) (k : Fin (n + 1)) : formal U (n + 1) ⟶ formal U n where
  f a := a.delete k
  φ a := Pi.lift (fun j : Fin n => Pi.π (fun i : Fin (n + 1) => U (a.val i)) (k.succAbove j))

theorem face_comp (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    face U (n + 1) j.succ ≫ face U n i =
      face U (n + 1) i.castSucc ≫ face U n j := by
  apply FormalCoproduct.hom_ext (funext (fun a => Index.delete_delete a hij))
  intro a
  exact Subsingleton.elim _ _

variable {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]
  (P : Cᵒᵖ ⥤ D)

def object (n : ℕ) : D := ((FormalCoproduct.evalOp C D).obj P).obj (op (formal U n))

def coface (n : ℕ) (k : Fin (n + 1)) : object U P n ⟶ object U P (n + 1) :=
  ((FormalCoproduct.evalOp C D).obj P).map (face U n k).op

omit [Preadditive D] in
theorem coface_comp (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    coface U P n i ≫ coface U P (n + 1) j.succ =
      coface U P n j ≫ coface U P (n + 1) i.castSucc := by
  let F := (FormalCoproduct.evalOp C D).obj P
  change F.map (face U n i).op ≫ F.map (face U (n + 1) j.succ).op =
    F.map (face U n j).op ≫ F.map (face U (n + 1) i.castSucc).op
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, face_comp U n hij]

omit [Preadditive D] in
theorem coface_comp' (n : ℕ) {i : Fin (n + 2)} {j : Fin (n + 1)}
    (hij : i ≤ j.castSucc) :
    coface U P n (i.castLT (lt_of_le_of_lt hij j.is_lt)) ≫ coface U P (n + 1) j.succ =
      coface U P n j ≫ coface U P (n + 1) i := by
  have hle : i.castLT (lt_of_le_of_lt hij j.is_lt) ≤ j := by
    rw [Fin.le_iff_val_le_val] at hij ⊢
    exact hij
  simpa using coface_comp U P n hle

def differential (n : ℕ) : object U P n ⟶ object U P (n + 1) :=
  ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • coface U P n k

theorem differential_comp (n : ℕ) : differential U P n ≫ differential U P (n + 1) = 0 := by
  dsimp [differential]
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  let T : Finset (Fin (n + 2) × Fin (n + 1)) := {ij | (ij.1 : ℕ) ≤ (ij.2 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl T,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : Fin (n + 2) × Fin (n + 1), ij ∈ T → Fin (n + 2) × Fin (n + 1) :=
    fun ij hij => (ij.2.succ, Fin.castLT ij.1
      (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.2)))
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [T, φ, Finset.compl_filter, Finset.mem_filter_univ,
      Fin.val_succ, Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ, Fin.castSucc_castLT] using!
      congr_arg Fin.castSucc (congr_arg Prod.snd h),
      by simpa [φ] using! congr_arg Prod.fst h⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [T, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(Fin.castSucc j', i'.pred (by
      rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij')), ?_, ?_⟩
    · simpa [T] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.succ_pred, Fin.castLT_castSucc]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, Fin.val_castLT, pow_add, pow_one,
        mul_neg, neg_mul, neg_neg, mul_one]
      apply mul_comm
    · rw [coface_comp' U P n]
      simpa [T] using! hij

def complex : CochainComplex D ℕ :=
  CochainComplex.of (object U P) (differential U P) (differential_comp U P)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.Cech
