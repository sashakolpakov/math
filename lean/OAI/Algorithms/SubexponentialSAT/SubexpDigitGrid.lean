import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBasePUnranking
import OAI.Algorithms.SubexponentialSAT.SubexpTableInterpolation

namespace OAI.Algorithms

/-!
# Exact order of the machine's base-p table rows

The unranker emits the least significant base-p digit first. The row builder
visits ascending ranks and prepends answers, so its final table uses descending
ranks. This file names that exact order and proves that it enumerates every
label vector once. Interpolation is unchanged by its permutation of `grid`.
-/

namespace SubexponentialSAT.SubexpDigitGrid

open SubexpBasePUnranking (numericDigits)
open SubexpTableInterpolation

/-- Split off the first digit of a nonempty label vector. -/
def splitVector (p k : ℕ) :
    List.Vector (Fin p) (k + 1) ≃ Fin p × List.Vector (Fin p) k where
  toFun v := (v.head, v.tail)
  invFun v := List.Vector.cons v.1 v.2
  left_inv v := List.Vector.cons_head_tail v
  right_inv v := by cases v; simp

/-- A genuine finite bijection, with the first coordinate the fastest digit.
It also handles empty vectors and empty alphabets without extra hypotheses. -/
def rankEquiv (p : ℕ) : (k : ℕ) → Fin (p ^ k) ≃ List.Vector (Fin p) k
  | 0 => by
      simpa only [pow_zero] using
        ({ toFun := fun _ => List.Vector.nil
           invFun := fun _ => (0 : Fin 1)
           left_inv := fun _ => Subsingleton.elim _ _
           right_inv := fun _ => Subsingleton.elim _ _ } :
          Fin 1 ≃ List.Vector (Fin p) 0)
  | k + 1 =>
      (finCongr (pow_succ p k)).trans <|
        finProdFinEquiv.symm.trans <|
          (Equiv.prodComm (Fin (p ^ k)) (Fin p)).trans <|
            (Equiv.prodCongr (Equiv.refl (Fin p)) (rankEquiv p k)).trans
              (splitVector p k).symm

/-- The vector bijection agrees exactly with repeated remainder/division in
the actual unranker. -/
theorem rankEquiv_values (p k : ℕ) (r : Fin (p ^ k)) :
    ((rankEquiv p k r).toList.map Fin.val) = numericDigits p k r.val := by
  induction k with
  | zero =>
      have h : rankEquiv p 0 r = List.Vector.nil := Subsingleton.elim _ _
      rw [h]
      rfl
  | succ k ih =>
      change r.val % p ::
        ((rankEquiv p k ((finCongr (pow_succ p k) r).divNat)).toList.map Fin.val) =
        r.val % p :: numericDigits p k (r.val / p)
      exact congrArg (List.cons (r.val % p))
        (ih ((finCongr (pow_succ p k) r).divNat))

/-- Label vectors in the order in which the rank counter visits them. -/
def ascending (p k : ℕ) : List (List.Vector (Fin p) k) :=
  (List.finRange (p ^ k)).map (rankEquiv p k)

/-- Label vectors in the order produced by prepending successive rows. -/
def descending (p k : ℕ) : List (List.Vector (Fin p) k) :=
  (ascending p k).reverse

@[simp] theorem ascending_length (p k : ℕ) : (ascending p k).length = p ^ k := by
  simp [ascending]

@[simp] theorem descending_length (p k : ℕ) : (descending p k).length = p ^ k := by
  simp [descending]

theorem ascending_nodup (p k : ℕ) : (ascending p k).Nodup :=
  (List.nodup_finRange (p ^ k)).map (rankEquiv p k).injective

theorem descending_nodup (p k : ℕ) : (descending p k).Nodup := by
  simpa [descending] using ascending_nodup p k

@[simp] theorem mem_ascending (p k : ℕ) (v : List.Vector (Fin p) k) :
    v ∈ ascending p k := by
  apply List.mem_map.mpr
  exact ⟨(rankEquiv p k).symm v, List.mem_finRange _, (rankEquiv p k).apply_symm_apply v⟩

@[simp] theorem mem_descending (p k : ℕ) (v : List.Vector (Fin p) k) :
    v ∈ descending p k := by simp [descending]

theorem ascending_values (p k : ℕ) :
    (ascending p k).map (fun v => v.toList.map Fin.val) =
      (List.range (p ^ k)).map (numericDigits p k) := by
  calc
    _ = (List.finRange (p ^ k)).map (fun r => numericDigits p k r.val) := by
      simp only [ascending, List.map_map]
      apply List.map_congr_left
      intro r _
      exact rankEquiv_values p k r
    _ = (List.range (p ^ k)).map (numericDigits p k) := by
      rw [← List.map_coe_finRange (p ^ k), List.map_map]
      rfl

/-- Exact numeric labels of the physical, prepended row stream. -/
theorem descending_values (p k : ℕ) :
    (descending p k).map (fun v => v.toList.map Fin.val) =
      (List.range (p ^ k)).reverse.map (numericDigits p k) := by
  simp only [descending, List.map_reverse, ascending_values]

theorem ascending_perm_grid (p k : ℕ) : (ascending p k).Perm (grid p k) := by
  rw [List.perm_ext_iff_of_nodup (ascending_nodup p k) (grid_nodup p k)]
  intro v
  exact iff_of_true (mem_ascending p k v) (grid_mem p k v)

/-- The machine order is a permutation, not a positional identification,
of the older first-coordinate-slowest Cartesian grid. -/
theorem descending_perm_grid (p k : ℕ) : (descending p k).Perm (grid p k) :=
  (List.reverse_perm (ascending p k)).trans (ascending_perm_grid p k)

/-- A table with each answer attached to its actual numeric label vector. -/
def rows {p k : ℕ} {R : Type*} (f : List.Vector (Fin p) k → R) : List (Row p k R) :=
  (descending p k).map (fun a => ⟨a, f a⟩)

@[simp] theorem rows_length {p k : ℕ} {R : Type*}
    (f : List.Vector (Fin p) k → R) : (rows f).length = p ^ k := by
  simp [rows]

theorem rows_perm_fullRows {p k : ℕ} {R : Type*}
    (f : List.Vector (Fin p) k → R) : (rows f).Perm (fullRows f) :=
  (descending_perm_grid p k).map (fun a => (⟨a, f a⟩ : Row p k R))

section Semantics

variable {p k : ℕ} {R : Type*} [CommRing R]

theorem tablePolynomial_rows (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (f : List.Vector (Fin p) k → R) :
    tablePolynomial v hu (rows f) = tablePolynomial v hu (fullRows f) :=
  ((rows_perm_fullRows f).map (rowPolynomial v hu)).sum_eq

theorem rows_eq_mvInterpolate (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (f : (Fin k → Fin p) → R) :
    tablePolynomial v hu (rows (fun a => f a.get)) =
      TableInterpolation.mvInterpolate v hu f := by
  rw [tablePolynomial_rows]
  exact fullRows_eq_mvInterpolate v hu f

theorem lookupRows_rows (f : List.Vector (Fin p) k → R)
    (a : List.Vector (Fin p) k) : lookupRows (rows f) a = f a := by
  calc
    _ = lookupRows (fullRows f) a :=
      ((rows_perm_fullRows f).map (fun row => if row.labels = a then row.value else 0)).sum_eq
    _ = f a := lookupRows_fullRows f a

end Semantics

end SubexponentialSAT.SubexpDigitGrid

end OAI.Algorithms
