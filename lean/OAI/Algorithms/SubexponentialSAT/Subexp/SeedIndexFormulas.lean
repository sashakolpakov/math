import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan

namespace OAI.Algorithms

/-! # Numeric seed positions in the explicit finite-index enumeration -/

namespace SubexponentialSAT.Subexp.SeedIndexFormulas

open AssignmentEnumeration
open SubexponentialSAT.LocalExpectation (indexCode)

theorem idxOf_map_injective {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (xs : List A) (x : A) :
    (xs.map f).idxOf (f x) = xs.idxOf x := by
  let _ : BEq A := instBEqOfDecidableEq
  let _ : BEq B := instBEqOfDecidableEq
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons]
    by_cases h : y = x
    · subst y
      simp
    · rw [List.idxOf_cons_ne _ (fun hh => h (hf hh)), List.idxOf_cons_ne _ h, ih]

theorem idxOf_sum_left {A B : Type*} [DecidableEq A] [DecidableEq B]
    (xs : List A) (ys : List B) (x : A) (hx : x ∈ xs) :
    indexCode (sumList xs ys) (.inl x) = indexCode xs x := by
  let _ : BEq A := instBEqOfDecidableEq
  let _ : BEq B := instBEqOfDecidableEq
  let _ : BEq (A ⊕ B) := instBEqOfDecidableEq
  unfold sumList indexCode
  rw [List.idxOf_append_of_mem (l₂ := ys.map Sum.inr)
    (show (Sum.inl x : A ⊕ B) ∈ xs.map Sum.inl from List.mem_map.mpr ⟨x, hx, rfl⟩)]
  exact idxOf_map_injective Sum.inl Sum.inl_injective xs x

theorem idxOf_sum_right {A B : Type*} [DecidableEq A] [DecidableEq B]
    (xs : List A) (ys : List B) (y : B) :
    indexCode (sumList xs ys) (.inr y) = xs.length + indexCode ys y := by
  let _ : BEq A := instBEqOfDecidableEq
  let _ : BEq B := instBEqOfDecidableEq
  let _ : BEq (A ⊕ B) := instBEqOfDecidableEq
  unfold sumList indexCode
  rw [List.idxOf_append_of_notMem (l₁ := xs.map Sum.inl) (l₂ := ys.map Sum.inr)
    (a := (Sum.inr y : A ⊕ B)) (by simp), List.length_map]
  rw [idxOf_map_injective Sum.inr Sum.inr_injective]

theorem idxOf_product {A B : Type*} [DecidableEq A] [DecidableEq B]
    (xs : List A) (ys : List B) (x : A) (y : B) (hx : x ∈ xs) (hy : y ∈ ys) :
    indexCode (xs.product ys) (x, y) = indexCode xs x * ys.length + indexCode ys y := by
  let _ : BEq A := instBEqOfDecidableEq
  let _ : BEq B := instBEqOfDecidableEq
  let _ : BEq (A × B) := instBEqOfDecidableEq
  unfold indexCode
  revert hx
  induction xs with
  | nil => simp
  | cons z zs ih =>
    intro hx
    change indexCode ((ys.map fun b => (z, b)) ++ zs.product ys) (x, y) = _
    unfold indexCode
    by_cases h : z = x
    · subst z
      rw [List.idxOf_append_of_mem (l₂ := zs.product ys)
        (show (x, y) ∈ ys.map (fun b => (x, b)) from List.mem_map.mpr ⟨y, hy, rfl⟩)]
      rw [idxOf_map_injective (fun b => (x, b)) (by intro a b hab; exact (Prod.mk.inj hab).2)]
      simp
    · rw [List.idxOf_append_of_notMem (l₁ := ys.map fun b => (z, b))
        (l₂ := zs.product ys) (a := (x, y)) (by simp [h]), List.length_map]
      rw [ih (by simpa only [List.mem_cons, Ne.symm h, false_or] using hx),
        List.idxOf_cons_ne _ h]
      rw [Nat.succ_eq_add_one]
      ring

theorem factorCode (D E Δ : ℕ) (e : Fin E) :
    seedCode (List.finRange D) (List.finRange E) Δ (.inl e) = e.val := by
  unfold seedCode seedIndices
  rw [idxOf_sum_left (List.finRange E)
    (sumList (List.finRange D) ((List.finRange D).product (List.finRange Δ))) e
    (List.mem_finRange e)]
  exact List.idxOf_finRange e

theorem headCode (D E Δ : ℕ) (v : Fin D) :
    seedCode (List.finRange D) (List.finRange E) Δ (.inr (.inl v)) = E + v.val := by
  unfold seedCode seedIndices
  rw [idxOf_sum_right (List.finRange E)
    (sumList (List.finRange D) ((List.finRange D).product (List.finRange Δ))) (.inl v),
    idxOf_sum_left (List.finRange D) ((List.finRange D).product (List.finRange Δ)) v
      (List.mem_finRange v)]
  simp [indexCode]

theorem paddingCode (D E Δ : ℕ) (v : Fin D) (i : Fin Δ) :
    seedCode (List.finRange D) (List.finRange E) Δ (.inr (.inr (v, i))) =
      E + D + v.val * Δ + i.val := by
  unfold seedCode seedIndices
  rw [idxOf_sum_right (List.finRange E)
    (sumList (List.finRange D) ((List.finRange D).product (List.finRange Δ))) (.inr (v, i)),
    idxOf_sum_right (List.finRange D) ((List.finRange D).product (List.finRange Δ)) (v, i),
    idxOf_product _ _ _ _ (List.mem_finRange v) (List.mem_finRange i)]
  simp only [indexCode, List.length_finRange, List.idxOf_finRange]
  omega

end SubexponentialSAT.Subexp.SeedIndexFormulas

end OAI.Algorithms
