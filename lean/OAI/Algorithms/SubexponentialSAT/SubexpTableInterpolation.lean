import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.TableInterpolation
import OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm
import OAI.Algorithms.SubexponentialSAT.Algorithm
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialCost
import OAI.Algorithms.SubexponentialSAT.NilpotentDefect

namespace OAI.Algorithms

/-!
# Uniform executable table interpolation

Every parameter in the bounds below is allowed to grow. Coefficient arithmetic,
inverse calls, syntax size, and encoded data length are kept separate from
primitive Turing-machine runtime.
-/

namespace SubexponentialSAT.SubexpTableInterpolation

open scoped BigOperators
open Polynomial


variable {R A S : Type*}

/-- A measured map which evaluates each input and each tail exactly once. -/
def mapWithCost {α β : Type*} (f : α → β × ℕ) : List α → List β × ℕ
  | [] => ([], 0)
  | x :: xs =>
      let y := f x
      let rest := mapWithCost f xs
      (y.1 :: rest.1, y.2 + rest.2)

@[simp] theorem mapWithCost_value {α β : Type*} (f : α → β × ℕ) (xs : List α) :
    (mapWithCost f xs).1 = xs.map (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mapWithCost, ih]

@[simp] theorem mapWithCost_length {α β : Type*} (f : α → β × ℕ) (xs : List α) :
    (mapWithCost f xs).1.length = xs.length := by simp

theorem mapWithCost_cost_le {α β : Type*} (f : α → β × ℕ) (xs : List α)
    (C : ℕ) (h : ∀ x ∈ xs, (f x).2 ≤ C) :
    (mapWithCost f xs).2 ≤ xs.length * C := by
  revert h
  induction xs with
  | nil => intro h; simp [mapWithCost]
  | cons x xs ih =>
      intro h
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simpa only [mapWithCost, List.length_cons, Nat.add_mul, one_mul, Nat.add_comm] using
        Nat.add_le_add hx ht

section Basis

variable [CommRing R] {p : ℕ}

/-- One normalized linear factor. The inverse is supplied as stored data.
The two charged operations are one multiplication and one negation. -/
def factorWithCost (v : Fin p → R) (d : Fin p → R) (i j : Fin p) :
    List R × ℕ :=
  if i = j then ([1], 0)
  else
    let inverse := d j
    ([-(inverse * v j), inverse], 2)

def basisWithCost (v : Fin p → R) (d : Fin p → R) (i : Fin p) :
    List R × ℕ :=
  let factors := mapWithCost (factorWithCost v d i) (List.finRange p)
  let result := PolynomialAlgorithm.productWithCost factors.1
  (result.1, factors.2 + result.2)

/-- Fixed polynomial in the number of labels, not a fixed-parameter constant. -/
def basisBudget (p : ℕ) : ℕ := 2 * p + 4 * p * (1 + 2 * p)

theorem factorWithCost_length (v : Fin p → R) (d : Fin p → R) (i j : Fin p) :
    (factorWithCost v d i j).1.length ≤ 2 := by
  unfold factorWithCost
  split <;> simp

theorem factorWithCost_cost (v : Fin p → R) (d : Fin p → R) (i j : Fin p) :
    (factorWithCost v d i j).2 ≤ 2 := by
  unfold factorWithCost
  split <;> simp

theorem basisWithCost_length (v : Fin p → R) (d : Fin p → R) (i : Fin p) :
    (basisWithCost v d i).1.length ≤ 1 + 2 * p := by
  have h : ∀ P ∈ (mapWithCost (factorWithCost v d i) (List.finRange p)).1,
      P.length ≤ 2 := by
    intro P hP
    simp only [mapWithCost_value, List.mem_map] at hP
    obtain ⟨j, hj, rfl⟩ := hP
    exact factorWithCost_length v d i j
  simpa [basisWithCost, Nat.mul_comm] using
    PolynomialAlgorithm.productWithCost_length_le
      (mapWithCost (factorWithCost v d i) (List.finRange p)).1 2 h

theorem basisWithCost_cost (v : Fin p → R) (d : Fin p → R) (i : Fin p) :
    (basisWithCost v d i).2 ≤ basisBudget p := by
  have hf := mapWithCost_cost_le (factorWithCost v d i) (List.finRange p) 2
    (fun j _ => factorWithCost_cost v d i j)
  have hp := PolynomialAlgorithm.productWithCost_cost_le
    (mapWithCost (factorWithCost v d i) (List.finRange p)).1 2 (by
      intro P hP
      simp only [mapWithCost_value, List.mem_map] at hP
      obtain ⟨j, hj, rfl⟩ := hP
      exact factorWithCost_length v d i j)
  change _ + _ ≤ _
  simpa [basisBudget, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    Nat.add_le_add hf hp

theorem factorWithCost_denote (v : Fin p → R) (d : Fin p → R) (i j : Fin p) :
    PolynomialAlgorithm.denote (factorWithCost v d i j).1 =
      if i = j then 1 else C (d j) * (X - C (v j)) := by
  unfold factorWithCost
  split
  · simp [PolynomialAlgorithm.denote]
  · simp [PolynomialAlgorithm.denote]
    ring

theorem inverse_eq_invDiff (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (d : Fin p → R) (i : Fin p)
    (hd : ∀ j, i ≠ j → d j * (v i - v j) = 1)
    (j : Fin p) (hij : i ≠ j) :
    d j = TableInterpolation.invDiff v hu i j := by
  apply left_inv_eq_right_inv (hd j hij)
  simpa [mul_comm] using TableInterpolation.invDiff_mul v hu hij

theorem basisWithCost_denote (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (d : Fin p → R) (i : Fin p)
    (hd : ∀ j, i ≠ j → d j * (v i - v j) = 1) :
    PolynomialAlgorithm.denote (basisWithCost v d i).1 = TableInterpolation.basis v hu i := by
  change PolynomialAlgorithm.denote (PolynomialAlgorithm.productWithCost _).1 = _
  rw [PolynomialAlgorithm.denote_productWithCost, mapWithCost_value, List.map_map]
  simp only [Function.comp_def, factorWithCost_denote]
  rw [← Fin.prod_univ_def]
  rw [← Finset.prod_erase Finset.univ
    (f := fun j => if i = j then (1 : Polynomial R) else C (d j) * (X - C (v j)))
    (a := i) (by simp)]
  unfold TableInterpolation.basis
  apply Finset.prod_congr rfl
  intro j hj
  have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  simp only [ite_eq_right hij, TableInterpolation.basisDivisor, inverse_eq_invDiff v hu d i hd j hij]

/-- All basis rows are computed once and retained as a dense coefficient cache. -/
def cacheWithCost (v : Fin p → R) (d : Fin p → Fin p → R) :
    List (List R) × ℕ :=
  mapWithCost (fun i => basisWithCost v (d i) i) (List.finRange p)

@[simp] theorem cacheWithCost_length (v : Fin p → R) (d : Fin p → Fin p → R) :
    (cacheWithCost v d).1.length = p := by simp [cacheWithCost]

theorem cacheWithCost_cost (v : Fin p → R) (d : Fin p → Fin p → R) :
    (cacheWithCost v d).2 ≤ p * basisBudget p := by
  simpa [cacheWithCost] using mapWithCost_cost_le
    (fun i => basisWithCost v (d i) i) (List.finRange p) (basisBudget p)
    (fun i _ => basisWithCost_cost v (d i) i)

theorem cacheWithCost_get (v : Fin p → R) (d : Fin p → Fin p → R) (i : Fin p) :
    (cacheWithCost v d).1.getD i.val [] = (basisWithCost v (d i) i).1 := by
  simp only [cacheWithCost, mapWithCost_value, ← List.ofFn_eq_map]
  simp [i.isLt]

theorem cacheWithCost_rows (v : Fin p → R) (d : Fin p → Fin p → R)
    (P : List R) (hP : P ∈ (cacheWithCost v d).1) :
    P.length ≤ 1 + 2 * p := by
  simp only [cacheWithCost, mapWithCost_value, List.mem_map] at hP
  obtain ⟨i, hi, rfl⟩ := hP
  exact basisWithCost_length v (d i) i

theorem cacheWithCost_correct (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (d : Fin p → Fin p → R)
    (hd : ∀ i j, i ≠ j → d i j * (v i - v j) = 1) (i : Fin p) :
    PolynomialAlgorithm.denote ((cacheWithCost v d).1.getD i.val []) = TableInterpolation.basis v hu i := by
  rw [cacheWithCost_get]
  exact basisWithCost_denote v hu (d i) i (hd i)

end Basis

/-- One explicitly stored row. Duplicate labels are interpreted by addition. -/
structure Row (p k : ℕ) (R : Type*) where
  labels : List.Vector (Fin p) k
  value : R

/-- Explicit Cartesian enumeration by reusing the already-built shorter grid. -/
def grid (p : ℕ) : (k : ℕ) → List (List.Vector (Fin p) k)
  | 0 => [List.Vector.nil]
  | k + 1 =>
      let shorter := grid p k
      ((List.finRange p).product shorter).map fun ab => List.Vector.cons ab.1 ab.2

@[simp] theorem grid_length (p k : ℕ) : (grid p k).length = p ^ k := by
  induction k with
  | zero => simp [grid]
  | succ k ih =>
      simp only [grid, List.length_map]
      change ((List.finRange p) ×ˢ grid p k).length = p ^ (k + 1)
      rw [List.length_product, List.length_finRange, ih, pow_succ']

theorem grid_mem (p k : ℕ) (a : List.Vector (Fin p) k) : a ∈ grid p k := by
  induction k with
  | zero =>
      have h : a = List.Vector.nil := Subsingleton.elim _ _
      simp [grid, h]
  | succ k ih =>
      apply List.mem_map.mpr
      refine ⟨(a.head, a.tail), ?_, List.Vector.cons_head_tail a⟩
      simp [ih]

theorem grid_nodup (p k : ℕ) : (grid p k).Nodup := by
  induction k with
  | zero => simp [grid]
  | succ k ih =>
      apply ((List.nodup_finRange p).product ih).map
      intro a b h
      apply Prod.ext
      · simpa using congrArg List.Vector.head h
      · simpa using congrArg List.Vector.tail h

/-- Construct the full explicit input table in exactly p^k rows. -/
def fullRows {p k : ℕ} (f : List.Vector (Fin p) k → R) : List (Row p k R) :=
  (grid p k).map fun a => ⟨a, f a⟩

@[simp] theorem fullRows_length {p k : ℕ} (f : List.Vector (Fin p) k → R) :
    (fullRows f).length = p ^ k := by simp [fullRows]

section Syntax

open Algorithm

variable {p k : ℕ}

/-- Horner syntax with a supplied coefficient representation. -/
def hornerExpr [Zero A] (literal : R → A) (x : Expr A) : List R → Expr A
  | [] => .lit 0
  | a :: as => .add (.lit (literal a)) (.mul x (hornerExpr literal x as))

def rowExpr [Zero A] [One A] (literal : R → A) (cache : List (List R))
    (row : Row p k R) (inputs : Fin k → Expr A) : Expr A :=
  .mul (.lit (literal row.value)) (Expr.product (List.ofFn fun i : Fin k =>
    hornerExpr literal (inputs i) (cache.getD (row.labels.get i).val [])))

/-- The tensor Lagrange table stays factored; no multivariate expansion occurs. -/
def tableExpr [Zero A] [One A] (literal : R → A) (cache : List (List R))
    (rows : List (Row p k R)) (inputs : Fin k → Expr A) : Expr A :=
  Expr.sum (rows.map fun row => rowExpr literal cache row inputs)

theorem hornerExpr_size [Zero A] (literal : R → A) (x : Expr A) (P : List R) :
    (hornerExpr literal x P).size = 1 + P.length * (x.size + 3) := by
  induction P with
  | nil => simp [hornerExpr, Expr.size]
  | cons a as ih => simp [hornerExpr, Expr.size, ih, Nat.add_mul]; omega

theorem sum_map_le_length_mul {α : Type*} (xs : List α) (f : α → ℕ) (C : ℕ)
    (h : ∀ x ∈ xs, f x ≤ C) : (xs.map f).sum ≤ xs.length * C := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simpa [Nat.add_mul, Nat.add_comm] using Nat.add_le_add hx ht

theorem rowExpr_size_le [Zero A] [One A] (literal : R → A) (cache : List (List R))
    (row : Row p k R) (inputs : Fin k → Expr A) (L X : ℕ)
    (hc : ∀ i : Fin p, (cache.getD i.val []).length ≤ L)
    (hx : ∀ i, (inputs i).size ≤ X) :
    (rowExpr literal cache row inputs).size ≤ 3 + k * (2 + L * (X + 3)) := by
  have hs := sum_map_le_length_mul
    (List.ofFn fun i : Fin k =>
      hornerExpr literal (inputs i) (cache.getD (row.labels.get i).val []))
    Expr.size (1 + L * (X + 3)) (by
      intro e he
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      rw [hornerExpr_size]
      gcongr
      · exact hc _
      · exact hx _)
  simp only [List.length_ofFn] at hs
  simp only [rowExpr, Expr.size, Expr.size_product, List.length_ofFn]
  nlinarith

theorem tableExpr_size_le [Zero A] [One A] (literal : R → A) (cache : List (List R))
    (rows : List (Row p k R)) (inputs : Fin k → Expr A) (L X : ℕ)
    (hc : ∀ i : Fin p, (cache.getD i.val []).length ≤ L)
    (hx : ∀ i, (inputs i).size ≤ X) :
    (tableExpr literal cache rows inputs).size ≤
      1 + rows.length * (4 + k * (2 + L * (X + 3))) := by
  have hs := sum_map_le_length_mul rows
    (fun row => (rowExpr literal cache row inputs).size)
    (3 + k * (2 + L * (X + 3)))
    (fun row _ => rowExpr_size_le literal cache row inputs L X hc hx)
  simp only [tableExpr, Expr.size_sum, List.map_map, List.length_map, Function.comp_def]
  nlinarith

theorem hornerExpr_correct [CommRing R] [Zero A] [CommRing S]
    (literal : R → A) (decode : A → S) (φ : R →+* S)
    (hz : decode 0 = 0) (hl : ∀ r, decode (literal r) = φ r)
    (x : Expr A) (P : List R) :
    ((hornerExpr literal x P).map decode).eval =
      Polynomial.eval₂ φ (x.map decode).eval (PolynomialAlgorithm.denote P) := by
  induction P with
  | nil => simp [hornerExpr, Expr.map, Expr.eval, hz, PolynomialAlgorithm.denote]
  | cons a as ih =>
      simp [hornerExpr, Expr.map, Expr.eval, hl, ih, PolynomialAlgorithm.denote]

theorem eval_map_sum [Zero A] [CommRing S] (decode : A → S) (hz : decode 0 = 0)
    (es : List (Expr A)) :
    ((Expr.sum es).map decode).eval = (es.map fun e => (e.map decode).eval).sum := by
  induction es with
  | nil => simp [Expr.sum, Expr.map, Expr.eval, hz]
  | cons e es ih => simp [Expr.sum, Expr.map, Expr.eval, ih]

theorem eval_map_product [One A] [CommRing S] (decode : A → S) (ho : decode 1 = 1)
    (es : List (Expr A)) :
    ((Expr.product es).map decode).eval = (es.map fun e => (e.map decode).eval).prod := by
  induction es with
  | nil => simp [Expr.product, Expr.map, Expr.eval, ho]
  | cons e es ih => simp [Expr.product, Expr.map, Expr.eval, ih]

end Syntax

section Semantics

variable [CommRing R] {p k : ℕ}

noncomputable def rowPolynomial (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (row : Row p k R) : MvPolynomial (Fin k) R :=
  MvPolynomial.C row.value * TableInterpolation.gridBasis v hu row.labels.get

noncomputable def tablePolynomial (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (rows : List (Row p k R)) : MvPolynomial (Fin k) R :=
  (rows.map (rowPolynomial v hu)).sum

def lookupRows (rows : List (Row p k R)) (a : List.Vector (Fin p) k) : R :=
  (rows.map fun row => if row.labels = a then row.value else 0).sum

theorem sum_lookup {α : Type*} [DecidableEq α] (f : α → R) (xs : List α)
    (a : α) (h : xs.Nodup) :
    (xs.map fun b => if b = a then f b else 0).sum =
      if a ∈ xs then f a else 0 := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
      obtain ⟨hb, ht⟩ := List.nodup_cons.mp h
      by_cases he : b = a
      · subst b
        simp [ih ht, hb]
      · simp [ih ht, he, Ne.symm he]

theorem lookupRows_fullRows (f : List.Vector (Fin p) k → R)
    (a : List.Vector (Fin p) k) : lookupRows (fullRows f) a = f a := by
  simp only [lookupRows, fullRows, List.map_map, Function.comp_def]
  rw [sum_lookup f _ a (grid_nodup p k), ite_eq_left (grid_mem p k a)]

theorem rowPolynomial_eval (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (row : Row p k R) (a : List.Vector (Fin p) k) :
    MvPolynomial.eval (fun i => v (a.get i)) (rowPolynomial v hu row) =
      if row.labels = a then row.value else 0 := by
  simp only [rowPolynomial, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    TableInterpolation.eval_gridBasis]
  have he : row.labels.get = a.get ↔ row.labels = a := by
    constructor
    · intro h; apply List.Vector.ext; exact congrFun h
    · intro h; rw [h]
  simp [he]

theorem tablePolynomial_eval (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (rows : List (Row p k R)) (a : List.Vector (Fin p) k) :
    MvPolynomial.eval (fun i => v (a.get i)) (tablePolynomial v hu rows) =
      lookupRows rows a := by
  induction rows with
  | nil => simp [tablePolynomial, lookupRows]
  | cons row rows ih =>
      simpa [tablePolynomial, lookupRows, rowPolynomial_eval] using ih

theorem fullRows_interpolate (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (f : List.Vector (Fin p) k → R) (a : List.Vector (Fin p) k) :
    MvPolynomial.eval (fun i => v (a.get i)) (tablePolynomial v hu (fullRows f)) = f a := by
  rw [tablePolynomial_eval, lookupRows_fullRows]

/-- The executable complete table is exactly the previously proved tensor
Lagrange polynomial, rather than merely agreeing with it on selected inputs. -/
theorem fullRows_eq_mvInterpolate (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (f : (Fin k → Fin p) → R) :
    tablePolynomial v hu (fullRows (fun a => f a.get)) =
      TableInterpolation.mvInterpolate v hu f := by
  classical
  let xs := (grid p k).map (fun a => a.get)
  have hn : xs.Nodup := (grid_nodup p k).map (Equiv.vectorEquivFin (Fin p) k).injective
  have hmem (a : Fin k → Fin p) : a ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨List.Vector.ofFn a, grid_mem p k _, funext (List.Vector.get_ofFn a)⟩
  have hu' : xs.toFinset = Finset.univ := by
    ext a
    simp [hmem a]
  calc
    _ = (xs.map fun a => MvPolynomial.C (f a) * TableInterpolation.gridBasis v hu a).sum := by
      simp only [tablePolynomial, fullRows, xs, rowPolynomial, List.map_map, Function.comp_def]
    _ = ∑ a ∈ xs.toFinset, MvPolynomial.C (f a) * TableInterpolation.gridBasis v hu a :=
      (List.sum_toFinset _ hn).symm
    _ = _ := by rw [hu']; rfl

theorem rowPolynomial_degreeOf (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (row : Row p k R) (i : Fin k) :
    (rowPolynomial v hu row).degreeOf i ≤ p - 1 := by
  exact (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
    (by simpa using TableInterpolation.degreeOf_gridBasis_le v hu row.labels.get i)

theorem tablePolynomial_degreeOf (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (rows : List (Row p k R)) (i : Fin k) :
    (tablePolynomial v hu rows).degreeOf i ≤ p - 1 := by
  induction rows with
  | nil => simp [tablePolynomial]
  | cons row rows ih =>
      change (rowPolynomial v hu row + tablePolynomial v hu rows).degreeOf i ≤ _
      exact (MvPolynomial.degreeOf_add_le _ _ _).trans
        (max_le (rowPolynomial_degreeOf v hu row i) ih)

theorem eval₂_mvBasis [CommRing S] (φ : R →+* S)
    (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (s : Fin k) (i : Fin p) (x : Fin k → S) :
    MvPolynomial.eval₂ φ x (TableInterpolation.mvBasis v hu s i) =
      Polynomial.eval₂ φ (x s) (TableInterpolation.basis v hu i) := by
  simp [TableInterpolation.mvBasis, TableInterpolation.basis,
    TableInterpolation.basisDivisor, MvPolynomial.eval₂_prod, Polynomial.eval₂_finsetProd]

theorem rowExpr_correct [Zero A] [One A] [CommRing S]
    (literal : R → A) (decode : A → S) (φ : R →+* S)
    (hz : decode 0 = 0) (ho : decode 1 = 1)
    (hl : ∀ r, decode (literal r) = φ r)
    (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (cache : List (List R))
    (hc : ∀ i : Fin p, PolynomialAlgorithm.denote (cache.getD i.val []) =
      TableInterpolation.basis v hu i)
    (row : Row p k R) (inputs : Fin k → Algorithm.Expr A) :
    ((rowExpr literal cache row inputs).map decode).eval =
      MvPolynomial.eval₂ φ (fun i => ((inputs i).map decode).eval)
        (rowPolynomial v hu row) := by
  simp only [rowExpr, Algorithm.Expr.map, Algorithm.Expr.eval, hl,
    eval_map_product decode ho, List.map_ofFn, Function.comp_def,
    hornerExpr_correct literal decode φ hz hl,
    hc, List.prod_ofFn, rowPolynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    TableInterpolation.gridBasis, MvPolynomial.eval₂_prod, eval₂_mvBasis]

theorem tableExpr_correct [Zero A] [One A] [CommRing S]
    (literal : R → A) (decode : A → S) (φ : R →+* S)
    (hz : decode 0 = 0) (ho : decode 1 = 1)
    (hl : ∀ r, decode (literal r) = φ r)
    (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (cache : List (List R))
    (hc : ∀ i : Fin p, PolynomialAlgorithm.denote (cache.getD i.val []) =
      TableInterpolation.basis v hu i)
    (rows : List (Row p k R)) (inputs : Fin k → Algorithm.Expr A) :
    ((tableExpr literal cache rows inputs).map decode).eval =
      MvPolynomial.eval₂ φ (fun i => ((inputs i).map decode).eval)
        (tablePolynomial v hu rows) := by
  induction rows with
  | nil => simp [tableExpr, Algorithm.Expr.sum, Algorithm.Expr.map, Algorithm.Expr.eval,
      hz, tablePolynomial]
  | cons row rows ih =>
      simpa [tableExpr, Algorithm.Expr.sum, Algorithm.Expr.map, Algorithm.Expr.eval,
        tablePolynomial, rowExpr_correct literal decode φ hz ho hl v hu cache hc] using
        congrArg (fun x =>
          MvPolynomial.eval₂ φ (fun i => ((inputs i).map decode).eval)
            (rowPolynomial v hu row) + x) ih

end Semantics

section IntegerPreprocessing

variable [CommRing R]

def geometricWithCost (z : R) (n : ℕ) : (R × R) × ℕ :=
  TruncatedInverse.geometricLoopWithCost 0 1 (fun x y => (x + y, 1))
    (fun x y => (x * y, 1)) z n

theorem geometricWithCost_sum (z : R) (n : ℕ) :
    (geometricWithCost z n).1.2 = ∑ j ∈ Finset.range n, z ^ j := by
  rw [geometricWithCost, TruncatedInverse.geometricLoopWithCost_value]
  exact (TruncatedInverse.geometricLoop_denote 0 1 (· + ·) (· * ·) z id
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) n).2

@[simp] theorem geometricWithCost_cost (z : R) (n : ℕ) :
    (geometricWithCost z n).2 = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (geometricWithCost z n).2 + 1 + 1 = _
      rw [ih]
      omega

/-- A linear Fermat power followed by a shared finite geometric correction.
Only ring additions, subtractions and multiplications occur. -/
def inverseWithCost (p μ : ℕ) (a : R) : R × ℕ :=
  let b := SubexpPolynomialCost.scalarPowerWithCost a (p - 2)
  let z := 1 - a * b.1
  let g := geometricWithCost z μ
  (b.1 * g.1.2, b.2 + 2 + g.2 + 1)

theorem inverseWithCost_value (p μ : ℕ) (a : R) :
    (inverseWithCost p μ a).1 =
      NilpotentDefect.geometricInverse a (a ^ (p - 2)) μ := by
  simp [inverseWithCost, geometricWithCost_sum, NilpotentDefect.geometricInverse]

theorem inverseWithCost_cost (p μ : ℕ) (a : R) :
    (inverseWithCost p μ a).2 ≤ p + 2 * μ + 3 := by
  simp only [inverseWithCost, SubexpPolynomialCost.scalarPower_cost,
    geometricWithCost_cost]
  omega

theorem fermat_defect_nilpotent (p μ : ℕ) (hp : p.Prime) (hμ : 0 < μ)
    (a : ZMod (p ^ μ)) (ha : LiftRing.baseReduction p μ hμ a ≠ 0) :
    (1 - a * a ^ (p - 2)) ^ μ = 0 := by
  have hpFact : Fact p.Prime := ⟨hp⟩
  have hpNeZero : NeZero p := ⟨hp.ne_zero⟩
  let ρ := LiftRing.baseReduction p μ hμ
  have hpow : ρ a * (ρ a) ^ (p - 2) = 1 := by
    rw [← pow_succ']
    have he : p - 2 + 1 = p - 1 := by have := hp.two_le; omega
    rw [he]
    exact @ZMod.pow_card_sub_one_eq_one p hpFact _ ha
  have hzero : ρ (1 - a * a ^ (p - 2)) = 0 := by
    simp only [map_sub, map_one, map_mul, map_pow, hpow, sub_self]
  obtain ⟨c, hc⟩ := (@LiftRing.baseReduction_eq_zero_iff p μ hpNeZero hμ _).mp hzero
  rw [hc, mul_pow]
  have hnil : (p : ZMod (p ^ μ)) ^ μ = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self _
  rw [hnil, zero_mul]

theorem inverseWithCost_correct (p μ : ℕ) (hp : p.Prime) (hμ : 0 < μ)
    (a : ZMod (p ^ μ)) (ha : LiftRing.baseReduction p μ hμ a ≠ 0) :
    (inverseWithCost p μ a).1 * a = 1 := by
  rw [inverseWithCost_value]
  exact NilpotentDefect.geometricInverse_mul a (a ^ (p - 2)) μ
    (fermat_defect_nilpotent p μ hp hμ a ha)

def integerInverseWithCost (p μ : ℕ) (i j : Fin p) : ZMod (p ^ μ) × ℕ :=
  if i = j then (0, 0) else
    let result := inverseWithCost p μ ((i.val : ZMod (p ^ μ)) - j.val)
    (result.1, 1 + result.2)

theorem integerInverseWithCost_cost (p μ : ℕ) (i j : Fin p) :
    (integerInverseWithCost p μ i j).2 ≤ p + 2 * μ + 4 := by
  unfold integerInverseWithCost
  split
  · simp
  · have := inverseWithCost_cost p μ ((i.val : ZMod (p ^ μ)) - j.val)
    dsimp only
    omega

theorem integerInverseWithCost_correct (p μ : ℕ) (hp : p.Prime) (hμ : 0 < μ)
    (i j : Fin p) (hij : i ≠ j) :
    (integerInverseWithCost p μ i j).1 *
      ((i.val : ZMod (p ^ μ)) - j.val) = 1 := by
  simp only [integerInverseWithCost, ite_eq_right hij]
  apply inverseWithCost_correct p μ hp hμ
  intro hzero
  apply hij
  apply Fin.ext
  have he : (i.val : ZMod p) = (j.val : ZMod p) :=
    sub_eq_zero.mp (by simpa only [map_sub, map_natCast] using hzero)
  have hm := (ZMod.natCast_eq_natCast_iff' i.val j.val p).mp he
  simpa only [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hm

def integerInversesWithCost (p μ : ℕ) : List (List (ZMod (p ^ μ))) × ℕ :=
  mapWithCost (fun i => mapWithCost (integerInverseWithCost p μ i) (List.finRange p))
    (List.finRange p)

theorem mapWithCost_getD_finRange {α : Type*} {n : ℕ} (f : Fin n → α × ℕ)
    (i : Fin n) (default : α) :
    (mapWithCost f (List.finRange n)).1.getD i.val default = (f i).1 := by
  simp only [mapWithCost_value, ← List.ofFn_eq_map]
  simp [i.isLt]

theorem integerInversesWithCost_get (p μ : ℕ) (i j : Fin p) :
    ((integerInversesWithCost p μ).1.getD i.val []).getD j.val 0 =
      (integerInverseWithCost p μ i j).1 := by
  simp only [integerInversesWithCost, mapWithCost_getD_finRange]

theorem integerInversesWithCost_cost (p μ : ℕ) :
    (integerInversesWithCost p μ).2 ≤ p * p * (p + 2 * μ + 4) := by
  have hrow (i : Fin p) := mapWithCost_cost_le (integerInverseWithCost p μ i)
    (List.finRange p) (p + 2 * μ + 4) (fun j _ => integerInverseWithCost_cost p μ i j)
  have h := mapWithCost_cost_le
    (fun i => mapWithCost (integerInverseWithCost p μ i) (List.finRange p))
    (List.finRange p) (p * (p + 2 * μ + 4)) (by
      intro i _
      simpa using hrow i)
  simpa only [integerInversesWithCost, List.length_finRange, Nat.mul_assoc] using h

/-- Complete table-basis preprocessing, including all inverses as explicit loops. -/
def integerCacheWithCost (p μ : ℕ) : List (List (ZMod (p ^ μ))) × ℕ :=
  let inverses := integerInversesWithCost p μ
  let cache := cacheWithCost (fun i : Fin p => (i.val : ZMod (p ^ μ)))
    (fun i j => (inverses.1.getD i.val []).getD j.val 0)
  (cache.1, inverses.2 + cache.2)

def preprocessingBudget (p μ : ℕ) : ℕ :=
  p * p * (p + 2 * μ + 4) + p * basisBudget p

theorem integerCacheWithCost_cost (p μ : ℕ) :
    (integerCacheWithCost p μ).2 ≤ preprocessingBudget p μ := by
  exact Nat.add_le_add (integerInversesWithCost_cost p μ) (cacheWithCost_cost _ _)

@[simp] theorem integerCacheWithCost_length (p μ : ℕ) :
    (integerCacheWithCost p μ).1.length = p := by
  exact cacheWithCost_length _ _

theorem integerCacheWithCost_rows (p μ : ℕ) (P : List (ZMod (p ^ μ)))
    (hP : P ∈ (integerCacheWithCost p μ).1) : P.length ≤ 1 + 2 * p := by
  exact cacheWithCost_rows _ _ P hP

theorem integerCacheWithCost_get_length (p μ : ℕ) (i : Fin p) :
    ((integerCacheWithCost p μ).1.getD i.val []).length ≤ 1 + 2 * p := by
  change ((cacheWithCost _ _).1.getD i.val []).length ≤ _
  rw [cacheWithCost_get]
  exact basisWithCost_length _ _ _

theorem integerCacheWithCost_correct (p μ : ℕ) (hp : p.Prime) (hμ : 0 < μ)
    (i : Fin p) :
    PolynomialAlgorithm.denote ((integerCacheWithCost p μ).1.getD i.val []) =
      TableInterpolation.basis (fun i : Fin p => (i.val : ZMod (p ^ μ)))
        (TableInterpolation.unitDifferences_zmod_integerLabels p μ hp) i := by
  apply cacheWithCost_correct
  intro i j hij
  rw [integerInversesWithCost_get]
  exact integerInverseWithCost_correct p μ hp hμ i j hij

theorem preprocessingBudget_uniform (p μ : ℕ) :
    preprocessingBudget p μ ≤ 16 * (p + μ + 1) ^ 3 := by
  unfold preprocessingBudget basisBudget
  ring_nf
  omega

end IntegerPreprocessing

section ChangeCoefficients

variable [CommRing R] [CommRing S] {p k : ℕ}

theorem denote_map (φ : R →+* S) (P : List R) :
    PolynomialAlgorithm.denote (P.map φ) = (PolynomialAlgorithm.denote P).map φ := by
  induction P with
  | nil => simp [PolynomialAlgorithm.denote]
  | cons a P ih => simp [PolynomialAlgorithm.denote, ih]

theorem basis_map (φ : R →+* S) (v : Fin p → R)
    (hu : TableInterpolation.UnitDifferences v) (i : Fin p) :
    (TableInterpolation.basis v hu i).map φ =
      TableInterpolation.basis (fun j => φ (v j)) (hu.map φ) i := by
  simp only [TableInterpolation.basis, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  have hd : ∀ j, i ≠ j → φ (TableInterpolation.invDiff v hu i j) *
      (φ (v i) - φ (v j)) = 1 := by
    intro j h
    simpa only [map_mul, map_sub, map_one] using congrArg φ (TableInterpolation.invDiff_mul v hu h)
  have hi := inverse_eq_invDiff (fun j => φ (v j)) (hu.map φ)
    (fun j => φ (TableInterpolation.invDiff v hu i j)) i hd j hij
  simp only [TableInterpolation.basisDivisor, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_sub, Polynomial.map_X, hi]

/-- Transport the computed base-ring cache through a supplied coefficient map. -/
def integerCacheMap (p μ : ℕ) (φ : ZMod (p ^ μ) →+* S) : List (List S) :=
  (integerCacheWithCost p μ).1.map (List.map φ)

theorem integerCacheMap_get (p μ : ℕ) (φ : ZMod (p ^ μ) →+* S) (i : Fin p) :
    (integerCacheMap p μ φ).getD i.val [] =
      ((integerCacheWithCost p μ).1.getD i.val []).map φ := by
  exact List.getD_map (integerCacheWithCost p μ).1 [] (List.map φ)

theorem integerCacheMap_length (p μ : ℕ) (φ : ZMod (p ^ μ) →+* S) (i : Fin p) :
    ((integerCacheMap p μ φ).getD i.val []).length ≤ 1 + 2 * p := by
  rw [integerCacheMap_get, List.length_map]
  exact integerCacheWithCost_get_length p μ i

theorem integerCacheMap_correct (p μ : ℕ) (hp : p.Prime) (hμ : 0 < μ)
    (φ : ZMod (p ^ μ) →+* S)
    (hu : TableInterpolation.UnitDifferences (fun i : Fin p => (i.val : S))) (i : Fin p) :
    PolynomialAlgorithm.denote ((integerCacheMap p μ φ).getD i.val []) =
      TableInterpolation.basis (fun i : Fin p => (i.val : S)) hu i := by
  rw [integerCacheMap_get, denote_map, integerCacheWithCost_correct p μ hp hμ, basis_map]
  simp only [map_natCast]

/-- The exact grid identity survives every coefficient-ring homomorphism. -/
theorem tablePolynomial_eval₂_labels (φ : R →+* S) (v : Fin p → R)
    (hu : TableInterpolation.UnitDifferences v) (rows : List (Row p k R))
    (a : List.Vector (Fin p) k) :
    MvPolynomial.eval₂ φ (fun i => φ (v (a.get i))) (tablePolynomial v hu rows) =
      φ (lookupRows rows a) := by
  have h := MvPolynomial.eval₂_comp_left φ (RingHom.id R)
    (fun i => v (a.get i)) (tablePolynomial v hu rows)
  calc
    _ = φ (MvPolynomial.eval (fun i => v (a.get i)) (tablePolynomial v hu rows)) := by
      simpa only [RingHom.comp_id, Function.comp_def, MvPolynomial.eval₂_id] using h.symm
    _ = _ := congrArg φ (tablePolynomial_eval v hu rows a)

/-- In particular, a path whose value at T=0 is an integer label has the exact
original table value at T=0, after any coefficient embedding. -/
theorem tableExpr_at_labels [Zero A] [One A]
    (literal : R → A) (decode : A → S) (φ : R →+* S)
    (hz : decode 0 = 0) (ho : decode 1 = 1)
    (hl : ∀ r, decode (literal r) = φ r)
    (v : Fin p → R) (hu : TableInterpolation.UnitDifferences v)
    (cache : List (List R))
    (hc : ∀ i : Fin p, PolynomialAlgorithm.denote (cache.getD i.val []) =
      TableInterpolation.basis v hu i)
    (rows : List (Row p k R)) (inputs : Fin k → Algorithm.Expr A)
    (a : List.Vector (Fin p) k)
    (ha : ∀ i, ((inputs i).map decode).eval = φ (v (a.get i))) :
    ((tableExpr literal cache rows inputs).map decode).eval = φ (lookupRows rows a) := by
  rw [tableExpr_correct literal decode φ hz ho hl v hu cache hc]
  simp only [ha]
  exact tablePolynomial_eval₂_labels φ v hu rows a

end ChangeCoefficients

section Reindexing

variable [CommRing R] {ι κ σ τ : Type*}
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]

omit [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ] in
theorem rename_mvBasis (e : σ ≃ τ) (v : ι → R)
    (hu : TableInterpolation.UnitDifferences v) (s : σ) (i : ι) :
    MvPolynomial.rename e (TableInterpolation.mvBasis v hu s i) =
      TableInterpolation.mvBasis v hu (e s) i := by
  simp [TableInterpolation.mvBasis, map_prod]

omit [DecidableEq σ] [DecidableEq τ] in
theorem rename_gridBasis (e : σ ≃ τ) (v : ι → R)
    (hu : TableInterpolation.UnitDifferences v) (a : σ → ι) :
    MvPolynomial.rename e (TableInterpolation.gridBasis v hu a) =
      TableInterpolation.gridBasis v hu (fun t => a (e.symm t)) := by
  simp only [TableInterpolation.gridBasis, map_prod]
  apply Fintype.prod_equiv e
  intro s
  simp only [rename_mvBasis, Equiv.symm_apply_apply]

theorem rename_mvInterpolate (e : σ ≃ τ) (v : ι → R)
    (hu : TableInterpolation.UnitDifferences v) (f : (σ → ι) → R) :
    MvPolynomial.rename e (TableInterpolation.mvInterpolate v hu f) =
      TableInterpolation.mvInterpolate v hu (fun a => f (fun s => a (e s))) := by
  let reindex : (σ → ι) ≃ (τ → ι) :=
    { toFun := fun a t => a (e.symm t)
      invFun := fun a s => a (e s)
      left_inv := by intro a; funext s; simp
      right_inv := by intro a; funext t; simp }
  simp only [TableInterpolation.mvInterpolate, map_sum, map_mul,
    MvPolynomial.rename_C, rename_gridBasis]
  apply Fintype.sum_equiv reindex
  intro a
  simp [reindex]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem reindexedUnits (e : ι ≃ κ) (v : κ → R) (hu : TableInterpolation.UnitDifferences v) :
    TableInterpolation.UnitDifferences (fun i => v (e i)) :=
  fun i j hij => hu (e i) (e j) (fun h => hij (e.injective h))

omit [Fintype ι] [Fintype κ] in
theorem invDiff_reindex (e : ι ≃ κ) (v : κ → R)
    (hu : TableInterpolation.UnitDifferences v) (i j : ι) (hij : i ≠ j) :
    TableInterpolation.invDiff (fun i => v (e i)) (reindexedUnits e v hu) i j =
      TableInterpolation.invDiff v hu (e i) (e j) := by
  apply left_inv_eq_right_inv (TableInterpolation.invDiff_mul _ _ hij)
  simpa only [mul_comm] using TableInterpolation.invDiff_mul v hu
    (fun h => hij (e.injective h))

omit [Fintype σ] [DecidableEq σ] in
theorem mvBasis_reindex (e : ι ≃ κ) (v : κ → R)
    (hu : TableInterpolation.UnitDifferences v) (s : σ) (i : ι) :
    TableInterpolation.mvBasis (fun i => v (e i)) (reindexedUnits e v hu) s i =
      TableInterpolation.mvBasis v hu s (e i) := by
  unfold TableInterpolation.mvBasis
  apply Finset.prod_equiv e
  · intro j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact not_congr e.injective.eq_iff.symm
  · intro j hj
    rw [invDiff_reindex e v hu i j (Finset.ne_of_mem_erase hj).symm]

omit [DecidableEq σ] in
theorem gridBasis_reindex (e : ι ≃ κ) (v : κ → R)
    (hu : TableInterpolation.UnitDifferences v) (a : σ → ι) :
    TableInterpolation.gridBasis (fun i => v (e i)) (reindexedUnits e v hu) a =
      TableInterpolation.gridBasis v hu (fun s => e (a s)) := by
  unfold TableInterpolation.gridBasis
  apply Finset.prod_congr rfl
  intro s _
  exact mvBasis_reindex e v hu s (a s)

theorem mvInterpolate_reindex (e : ι ≃ κ) (v : κ → R)
    (hu : TableInterpolation.UnitDifferences v) (f : (σ → κ) → R) :
    TableInterpolation.mvInterpolate (fun i => v (e i)) (reindexedUnits e v hu)
      (fun a => f (fun s => e (a s))) = TableInterpolation.mvInterpolate v hu f := by
  let reindex : (σ → ι) ≃ (σ → κ) :=
    { toFun := fun a s => e (a s)
      invFun := fun a s => e.symm (a s)
      left_inv := by intro a; funext s; simp
      right_inv := by intro a; funext s; simp }
  simp only [TableInterpolation.mvInterpolate]
  apply Fintype.sum_equiv reindex
  intro a
  rw [gridBasis_reindex e v hu a]
  rfl

/-- Direct bridge from explicit finite rows to a table on an arbitrary finite
scope and arbitrary finite label type. Both equivalences are supplied data. -/
theorem fullRows_reindexed {p k : ℕ} (scope : Fin k ≃ σ) (labels : Fin p ≃ ι)
    (v : ι → R) (hu : TableInterpolation.UnitDifferences v) (f : (σ → ι) → R) :
    tablePolynomial (fun i => v (labels i)) (reindexedUnits labels v hu)
      (fullRows (fun a => f (fun s => labels (a.get (scope.symm s))))) =
        MvPolynomial.rename scope.symm (TableInterpolation.mvInterpolate v hu f) := by
  rw [rename_mvInterpolate]
  rw [fullRows_eq_mvInterpolate (fun i => v (labels i)) (reindexedUnits labels v hu)
    (fun a => f (fun s => labels (a (scope.symm s))))]
  exact mvInterpolate_reindex labels v hu (fun a => f (fun s => a (scope.symm s)))

end Reindexing

section Encoding

open StackEncoding

variable {p k : ℕ}

/-- Coefficient followed by its fixed number of fixed-width integer labels. -/
def rowCode (coefficient : BlockCode R) (label : BlockCode (Fin p)) :
    BlockCode (Row p k R) where
  width := coefficient.width + k * label.width
  width_pos := by have := coefficient.width_pos; omega
  block row := coefficient.block row.value ++ encodeDataStack label row.labels.toList
  length_block row := by simp [coefficient.length_block]
  injective_block := by
    intro x y h
    have hv : x.value = y.value := by
      apply coefficient.injective_block
      simpa only [take_block_append] using congrArg (List.take coefficient.width) h
    have hl : x.labels = y.labels := by
      apply List.Vector.toList_injective
      apply encodeDataStack_injective label
      simpa only [drop_block_append] using congrArg (List.drop coefficient.width) h
    cases x
    cases y
    simp_all

/-- Zero padding gives each cached polynomial a fixed number of coefficient slots. -/
def pad [Zero R] (L : ℕ) (P : List R) : List R :=
  P ++ List.replicate (L - P.length) 0

theorem pad_length [Zero R] (L : ℕ) (P : List R) (h : P.length ≤ L) :
    (pad L P).length = L := by
  simp only [pad, List.length_append, List.length_replicate]
  omega

theorem denote_append_zeroes [CommRing R] (P : List R) (n : ℕ) :
    PolynomialAlgorithm.denote (P ++ List.replicate n 0) = PolynomialAlgorithm.denote P := by
  induction P with
  | nil =>
      induction n with
      | zero => rfl
      | succ n ih => simpa [List.replicate_succ, PolynomialAlgorithm.denote] using ih
  | cons a P ih => simp [PolynomialAlgorithm.denote, ih]

theorem denote_pad [CommRing R] (L : ℕ) (P : List R) :
    PolynomialAlgorithm.denote (pad L P) = PolynomialAlgorithm.denote P :=
  denote_append_zeroes P _

def encodeCache [Zero R] (coefficient : BlockCode R) (L : ℕ)
    (cache : List (List R)) : List Bool :=
  cache.flatMap fun P => encodeDataStack coefficient (pad L P)

theorem encodeCache_length [Zero R] (coefficient : BlockCode R) (L : ℕ)
    (cache : List (List R)) (h : ∀ P ∈ cache, P.length ≤ L) :
    (encodeCache coefficient L cache).length = cache.length * L * coefficient.width := by
  induction cache with
  | nil => simp [encodeCache]
  | cons P Ps ih =>
      have hp := h P (by simp)
      have ht := ih (fun Q hQ => h Q (by simp [hQ]))
      simpa [encodeCache, pad_length L P hp, Nat.add_mul, Nat.add_comm] using ht

/-- Parameters p,k,mu and the row count determine every block boundary. -/
def encodeTable [Zero R] (coefficient : BlockCode R) (label : BlockCode (Fin p))
    (L : ℕ) (cache : List (List R)) (rows : List (Row p k R)) : List Bool :=
  encodeCache coefficient L cache ++ encodeDataStack (rowCode coefficient label) rows

theorem encodeTable_length [Zero R] (coefficient : BlockCode R)
    (label : BlockCode (Fin p)) (L : ℕ) (cache : List (List R))
    (rows : List (Row p k R)) (h : ∀ P ∈ cache, P.length ≤ L) :
    (encodeTable coefficient label L cache rows).length =
      cache.length * L * coefficient.width +
        rows.length * (coefficient.width + k * label.width) := by
  simp [encodeTable, encodeCache_length coefficient L cache h, rowCode]

def integerTableEncoding (p μ : ℕ) [Fact p.Prime] (hμ : 0 < μ)
    (rows : List (Row p k (ZMod (p ^ μ)))) : List Bool :=
  encodeTable (SubexpLiftRing.baseCode p μ hμ)
    (codeOfEquiv (Equiv.refl (Fin p))) (1 + 2 * p) (integerCacheWithCost p μ).1 rows

theorem integerTableEncoding_length (p μ : ℕ) [Fact p.Prime] (hμ : 0 < μ)
    (rows : List (Row p k (ZMod (p ^ μ)))) :
    (integerTableEncoding p μ hμ rows).length =
      p * (1 + 2 * p) * (μ * (Nat.log 2 p + 1)) +
        rows.length * (μ * (Nat.log 2 p + 1) + k * (Nat.log 2 p + 1)) := by
  rw [integerTableEncoding, encodeTable_length]
  · simp [SubexpLiftRing.baseCode, SubexpLiftRing.baseWidth, codeOfEquiv, codingWidth]
  · exact integerCacheWithCost_rows p μ

end Encoding

end SubexponentialSAT.SubexpTableInterpolation

end OAI.Algorithms
