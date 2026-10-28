import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularArithmetic
import OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm
import OAI.Algorithms.SubexponentialSAT.SubexpTruncatedGeometric

namespace OAI.Algorithms

/-!
# Fixed-width bit padding and dense polynomial coefficients

The literal loader pads or truncates a flat payload to a whole number of
coefficient cells. This file identifies that operation at the cell level.
Preservation of a complete polynomial requires its degree to be below the
number of retained cells; this condition is explicit before any Taylor shift.
-/

namespace SubexponentialSAT.SubexpDensePaddingSpec

open ModularArithmetic

def padCells {C : Type*} (zero : C) : ℕ → List C → List C
  | 0, _ => []
  | n + 1, [] => zero :: padCells zero n []
  | n + 1, a :: as => a :: padCells zero n as

@[simp] theorem padCells_nil {C : Type*} (zero : C) (n : ℕ) :
    padCells zero n [] = List.replicate n zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [padCells, List.replicate_succ] using (congrArg (List.cons zero) ih)

theorem padCells_eq_take_append {C : Type*} (zero : C) (n : ℕ) (xs : List C) :
    padCells zero n xs = (xs ++ List.replicate n zero).take n := by
  induction n generalizing xs with
  | zero => simp [padCells]
  | succ n ih =>
      cases xs with
      | nil => simp [padCells, ih, List.replicate_succ]
      | cons a as =>
          simp only [padCells, List.cons_append, List.take_succ_cons, ih]
          congr 1
          simp only [List.take_append, List.take_replicate]
          congr 2 ; omega

@[simp] theorem padCells_length {C : Type*} (zero : C) (n : ℕ) (xs : List C) :
    (padCells zero n xs).length = n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => cases xs <;> simp [padCells, ih]

private theorem padTo_prefix (shape front rest input : List Bool)
    (hlen : shape.length = front.length) :
    padTo (shape ++ rest) (front ++ input) = front ++ padTo rest input := by
  induction shape generalizing front with
  | nil =>
      have hp : front = [] := List.length_eq_zero_iff.mp hlen.symm
      simp [hp]
  | cons bit shape ih =>
      cases front with
      | nil => simp at hlen
      | cons head tail =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          simpa only [List.cons_append, padTo] using congrArg (List.cons head) (ih tail hlen)

private theorem padTo_empty (shape : List Bool) :
    padTo shape [] = List.replicate shape.length false := by
  induction shape with
  | nil => rfl
  | cons bit rest ih => simp [padTo, ih, List.replicate_succ]

/-- The actual bit-loader operation agrees with truncation/padding of whole
coefficient cells, including zero-width and empty-input cases. -/
theorem padTo_flatten (cellCount width : ℕ) (words : List (List Bool))
    (hwidth : ∀ word ∈ words, word.length = width) :
    padTo (List.replicate (cellCount * width) false) words.flatten =
      (padCells (List.replicate width false) cellCount words).flatten := by
  induction cellCount generalizing words with
  | zero => simp [padCells, padTo]
  | succ n ih =>
      cases words with
      | nil =>
          simp only [List.flatten_nil, padTo_empty, List.length_replicate,
            padCells_nil, List.flatten_replicate_replicate]
      | cons word words =>
          have hw : word.length = width := hwidth word (by simp)
          rw [show (n + 1) * width = width + n * width by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm], List.replicate_add,
            List.flatten_cons, padTo_prefix _ word _ _ (by simpa using hw.symm)]
          simpa only [padCells, List.flatten_cons] using
            congrArg (fun xs => word ++ xs)
              (ih words (fun x hx => hwidth x (by simp [hx])))

/-- Specialization to an arbitrary fixed-width coefficient encoding. -/
theorem padTo_encoded {C : Type*} (encode : C → List Bool) (zero : C)
    (cellCount width : ℕ) (xs : List C)
    (hzero : encode zero = List.replicate width false)
    (hwidth : ∀ x ∈ xs, (encode x).length = width) :
    padTo (List.replicate (cellCount * width) false) (xs.map encode).flatten =
      ((padCells zero cellCount xs).map encode).flatten := by
  rw [padTo_flatten cellCount width (xs.map encode) (by
    intro word hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
    exact hwidth x hx)]
  have hmap (n : ℕ) (ys : List C) :
      padCells (List.replicate width false) n (ys.map encode) =
        (padCells zero n ys).map encode := by
    induction n generalizing ys with
    | zero => rfl
    | succ n ih => cases ys <;> simp [padCells, hzero, ih, List.replicate_succ]
  exact congrArg List.flatten (hmap cellCount xs)

section Denotation

variable {C R : Type*} [CommSemiring R]
variable (decode : C → R) (zero : C) (hzero : decode zero = 0)

include hzero

theorem coeff_padCells (cellCount : ℕ) (xs : List C) (i : ℕ) :
    PolynomialAlgorithm.coeff ((padCells zero cellCount xs).map decode) i =
      if i < cellCount then PolynomialAlgorithm.coeff (xs.map decode) i else 0 := by
  induction cellCount generalizing xs i with
  | zero => simp [padCells, PolynomialAlgorithm.coeff]
  | succ n ih =>
      cases xs <;> cases i <;>
        simp only [padCells, List.map_nil, List.map_cons, PolynomialAlgorithm.coeff,
          hzero, Nat.zero_lt_succ, ite_true, Nat.succ_lt_succ_iff, ih, ite_self]

theorem denote_padCells (cellCount : ℕ) (xs : List C) :
    PolynomialAlgorithm.denote ((padCells zero cellCount xs).map decode) =
      Truncation.trunc cellCount (PolynomialAlgorithm.denote (xs.map decode)) := by
  ext i
  simp only [PolynomialAlgorithm.coeff_denote, Truncation.coeff_trunc,
    coeff_padCells decode zero hzero]

/-- A full-row denotation is preserved only after the retained cell count
has been shown to exceed the complete row's degree. -/
theorem denote_padCells_of_degree_lt (cellCount : ℕ) (xs : List C)
    (hdegree : (PolynomialAlgorithm.denote (xs.map decode)).natDegree < cellCount) :
    PolynomialAlgorithm.denote ((padCells zero cellCount xs).map decode) =
      PolynomialAlgorithm.denote (xs.map decode) := by
  rw [denote_padCells decode zero hzero]
  ext i
  rw [Truncation.coeff_trunc]
  split_ifs with hi
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (hdegree.trans_le (by omega))).symm

end Denotation

section Expressions

variable {B S R : Type*} [CommRing R]

/-- Value-level execution with the same literal/add/multiply operations that
the postfix services refine. No denotation function is used during execution. -/
def evalWith (literal : B → S) (add mul : S → S → S) : Algorithm.Expr B → S
  | .lit b => literal b
  | .add e f => add (evalWith literal add mul e) (evalWith literal add mul f)
  | .mul e f => mul (evalWith literal add mul e) (evalWith literal add mul f)

/-- Truncated arithmetic is sound even if intermediate expressions have
higher degree than the final row. The local invariant can be fixed cell
length, so arithmetic laws are needed only on well-formed operands. -/
theorem evalWith_correct (cellCount : ℕ) (Good : S → Prop)
    (literal : B → S) (add mul : S → S → S)
    (denote : S → Polynomial R) (meaning : B → Polynomial R)
    (hliteral : ∀ b, Good (literal b) ∧
      denote (literal b) = Truncation.trunc cellCount (meaning b))
    (hadd : ∀ x y, Good x → Good y → Good (add x y) ∧
      denote (add x y) = denote x + denote y)
    (hmul : ∀ x y, Good x → Good y → Good (mul x y) ∧
      denote (mul x y) = Truncation.trunc cellCount (denote x * denote y))
    (e : Algorithm.Expr B) :
    Good (evalWith literal add mul e) ∧
      denote (evalWith literal add mul e) =
        Truncation.trunc cellCount ((e.map meaning).eval) := by
  induction e with
  | lit b => exact hliteral b
  | add e f he hf =>
      obtain ⟨hg, hd⟩ := hadd _ _ he.1 hf.1
      refine ⟨hg, ?_⟩
      change denote (add (evalWith literal add mul e) (evalWith literal add mul f)) =
        Truncation.trunc cellCount ((e.map meaning).eval + (f.map meaning).eval)
      rw [hd, he.2, hf.2, Truncation.trunc_add]
  | mul e f he hf =>
      obtain ⟨hg, hd⟩ := hmul _ _ he.1 hf.1
      refine ⟨hg, ?_⟩
      change denote (mul (evalWith literal add mul e) (evalWith literal add mul f)) =
        Truncation.trunc cellCount ((e.map meaning).eval * (f.map meaning).eval)
      rw [hd, he.2, hf.2, SubexpTruncatedGeometric.trunc_mul_trunc]

/-- The final degree bound restores the full row, without a degree bound on
every intermediate product and without commuting the residue section with
field arithmetic. Coefficientwise lifting follows this theorem. -/
theorem evalWith_full_row (cellCount : ℕ) (Good : S → Prop)
    (literal : B → S) (add mul : S → S → S)
    (denote : S → Polynomial R) (meaning : B → Polynomial R)
    (hliteral : ∀ b, Good (literal b) ∧
      denote (literal b) = Truncation.trunc cellCount (meaning b))
    (hadd : ∀ x y, Good x → Good y → Good (add x y) ∧
      denote (add x y) = denote x + denote y)
    (hmul : ∀ x y, Good x → Good y → Good (mul x y) ∧
      denote (mul x y) = Truncation.trunc cellCount (denote x * denote y))
    (e : Algorithm.Expr B) (hdegree : ((e.map meaning).eval).natDegree < cellCount) :
    denote (evalWith literal add mul e) = (e.map meaning).eval := by
  rw [(evalWith_correct cellCount Good literal add mul denote meaning hliteral hadd hmul e).2]
  ext i
  rw [Truncation.coeff_trunc]
  split_ifs with hi
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (hdegree.trans_le (by omega))).symm

end Expressions

end SubexponentialSAT.SubexpDensePaddingSpec

end OAI.Algorithms
