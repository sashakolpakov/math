import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-! The elementary update schedule implemented by the fixed convolution loop.
This module defines values only; it assigns no execution cost to them. -/

namespace SubexponentialSAT.TruncatedConvolution

variable {C : Type*}

/-- Add one product into one existing coefficient slot. -/
def addProduct (add mul : C → C → C) (i : ℕ) (a b : C) (acc : List C) : List C :=
  acc.modify i (fun c => add (mul a b) c)

/-- A row of the triangular product schedule, beginning at output slot i. -/
def row (add mul : C → C → C) (a : C) : ℕ → List C → List C → List C
  | _, [], acc => acc
  | i, b :: bs, acc => row add mul a (i + 1) bs (addProduct add mul i a b acc)

/-- Fuel is the number of remaining output slots, so a row uses only that
many right-hand coefficients. All writes therefore have degree below D. -/
def rows (add mul : C → C → C) (Q : List C) : ℕ → ℕ → List C → List C → List C
  | _, 0, _, acc => acc
  | _, _ + 1, [], acc => acc
  | i, fuel + 1, a :: rest, acc =>
      rows add mul Q (i + 1) fuel rest (row add mul a i (Q.take (fuel + 1)) acc)

/-- Exactly D output slots; callers supply the actual zero coefficient. -/
def run (zero : C) (add mul : C → C → C) (D : ℕ) (P Q : List C) : List C :=
  rows add mul Q 0 D P (List.replicate D zero)

@[simp] theorem addProduct_length (add mul : C → C → C) (i : ℕ) (a b : C)
    (acc : List C) : (addProduct add mul i a b acc).length = acc.length := by
  simp [addProduct]

@[simp] theorem row_length (add mul : C → C → C) (a : C) (i : ℕ)
    (Q acc : List C) : (row add mul a i Q acc).length = acc.length := by
  induction Q generalizing i acc with
  | nil => rfl
  | cons b bs ih => simpa [row] using ih (i + 1) (addProduct add mul i a b acc)

@[simp] theorem rows_length (add mul : C → C → C) (Q : List C) (i fuel : ℕ)
    (P acc : List C) : (rows add mul Q i fuel P acc).length = acc.length := by
  induction fuel generalizing i P acc with
  | zero => rfl
  | succ fuel ih =>
      cases P with
      | nil => rfl
      | cons a rest => simpa [rows] using ih (i + 1) rest (row add mul a i (Q.take (fuel + 1)) acc)

@[simp] theorem run_length (zero : C) (add mul : C → C → C) (D : ℕ) (P Q : List C) :
    (run zero add mul D P Q).length = D := by
  simp [run]

end SubexponentialSAT.TruncatedConvolution

end OAI.Algorithms
