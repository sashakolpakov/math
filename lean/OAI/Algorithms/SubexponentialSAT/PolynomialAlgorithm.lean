import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Truncation

namespace OAI.Algorithms

/-!
# Executable dense univariate polynomial arithmetic

Lists store coefficients from constant term upwards. Trailing zeroes are allowed.
The instrumented algorithms return their value and the number of coefficient-ring
additions and multiplications they actually perform. List manipulation and primitive
bit costs are separate. Recursive results are bound once and reused.
-/

namespace SubexponentialSAT.PolynomialAlgorithm

variable {R : Type*}

section Algorithms

variable [Semiring R]

/-- Dense addition; unmatched tails are returned without scalar arithmetic. -/
def addWithCost : List R → List R → List R × ℕ
  | [], Q => (Q, 0)
  | P, [] => (P, 0)
  | a :: P, b :: Q =>
      let rest := addWithCost P Q
      ((a + b) :: rest.1, rest.2 + 1)

def add (P Q : List R) : List R := (addWithCost P Q).1

/-- One scalar multiplication for every stored coefficient. -/
def scaleWithCost (a : R) : List R → List R × ℕ
  | [] => ([], 0)
  | b :: P =>
      let rest := scaleWithCost a P
      ((a * b) :: rest.1, rest.2 + 1)

def scale (a : R) (P : List R) : List R := (scaleWithCost a P).1

/-- Schoolbook multiplication, with each partial product computed only once. -/
def mulWithCost : List R → List R → List R × ℕ
  | [], _ => ([], 0)
  | a :: P, Q =>
      let row := scaleWithCost a Q
      let rest := mulWithCost P Q
      let combined := addWithCost row.1 (0 :: rest.1)
      (combined.1, row.2 + rest.2 + combined.2)

def mul (P Q : List R) : List R := (mulWithCost P Q).1

/-- Sum a list of dense polynomials, computing each tail sum once. -/
def sumWithCost : List (List R) → List R × ℕ
  | [] => ([], 0)
  | P :: Ps =>
      let rest := sumWithCost Ps
      let combined := addWithCost P rest.1
      (combined.1, rest.2 + combined.2)

def sum (Ps : List (List R)) : List R := (sumWithCost Ps).1

/-- Multiply a list of dense polynomials, computing each tail product once. -/
def productWithCost : List (List R) → List R × ℕ
  | [] => ([1], 0)
  | P :: Ps =>
      let rest := productWithCost Ps
      let combined := mulWithCost P rest.1
      (combined.1, rest.2 + combined.2)

def product (Ps : List (List R)) : List R := (productWithCost Ps).1

/-- Horner evaluation uses one multiplication and one addition per coefficient. -/
def evalWithCost (x : R) : List R → R × ℕ
  | [] => (0, 0)
  | a :: P =>
      let rest := evalWithCost x P
      (a + x * rest.1, rest.2 + 2)

def eval (x : R) (P : List R) : R := (evalWithCost x P).1

/-- Polynomial Horner substitution at X+a. Each previous accumulator is
computed once, then multiplied by the stored linear polynomial [a, 1]. -/
def shiftWithCost (a : R) : List R → List R × ℕ
  | [] => ([], 0)
  | b :: P =>
      let rest := shiftWithCost a P
      let product := mulWithCost [a, 1] rest.1
      let combined := addWithCost [b] product.1
      (combined.1, rest.2 + product.2 + combined.2)

def shift (a : R) (P : List R) : List R := (shiftWithCost a P).1

/-- Truncation is just a prefix of the coefficient list. -/
def truncate (D : ℕ) (P : List R) : List R := P.take D

/-- Taking a prefix performs no coefficient-ring operations. -/
def truncateWithCost (D : ℕ) (P : List R) : List R × ℕ := (truncate D P, 0)

/-- Coefficient lookup, with zero beyond the stored list. -/
def coeff : List R → ℕ → R
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: P, n + 1 => coeff P n

@[simp] theorem addWithCost_cost (P Q : List R) :
    (addWithCost P Q).2 = min P.length Q.length := by
  induction P generalizing Q with
  | nil => simp [addWithCost]
  | cons a P ih =>
      cases Q with
      | nil => simp [addWithCost]
      | cons b Q => simp [addWithCost, ih ]

@[simp] theorem addWithCost_length (P Q : List R) :
    (addWithCost P Q).1.length = max P.length Q.length := by
  induction P generalizing Q with
  | nil => simp [addWithCost]
  | cons a P ih =>
      cases Q with
      | nil => simp [addWithCost]
      | cons b Q => simp [addWithCost, ih ]

@[simp] theorem length_add (P Q : List R) :
    (add P Q).length = max P.length Q.length := addWithCost_length P Q

@[simp] theorem scaleWithCost_cost (a : R) (P : List R) :
    (scaleWithCost a P).2 = P.length := by
  induction P with
  | nil => rfl
  | cons b P ih => simp [scaleWithCost, ih]

@[simp] theorem scaleWithCost_length (a : R) (P : List R) :
    (scaleWithCost a P).1.length = P.length := by
  induction P with
  | nil => rfl
  | cons b P ih => simp [scaleWithCost, ih]

@[simp] theorem length_scale (a : R) (P : List R) :
    (scale a P).length = P.length := scaleWithCost_length a P

theorem mulWithCost_length_le (P Q : List R) :
    (mulWithCost P Q).1.length ≤ P.length + Q.length := by
  induction P with
  | nil => simp [mulWithCost]
  | cons a P ih =>
      simp only [mulWithCost, addWithCost_length, scaleWithCost_length, List.length_cons]
      omega

theorem length_mul_le (P Q : List R) :
    (mul P Q).length ≤ P.length + Q.length := mulWithCost_length_le P Q

theorem mulWithCost_cost_le (P Q : List R) :
    (mulWithCost P Q).2 ≤ 2 * P.length * Q.length := by
  induction P with
  | nil => simp [mulWithCost]
  | cons a P ih =>
      simp only [mulWithCost, scaleWithCost_cost, addWithCost_cost,
        scaleWithCost_length, List.length_cons]
      calc
        Q.length + (mulWithCost P Q).2 +
            min Q.length ((mulWithCost P Q).1.length + 1)
            ≤ Q.length + (2 * P.length * Q.length) + Q.length :=
          Nat.add_le_add (Nat.add_le_add_left ih _) (Nat.min_le_left _ _)
        _ = 2 * (P.length + 1) * Q.length := by ring

theorem sumWithCost_length_le (Ps : List (List R)) (L : ℕ)
    (h : ∀ P ∈ Ps, P.length ≤ L) :
    (sumWithCost Ps).1.length ≤ L := by
  revert h
  induction Ps with
  | nil => intro h; simp [sumWithCost]
  | cons P Ps ih =>
      intro h
      have hP : P.length ≤ L := h P (by simp)
      have hPs : ∀ Q ∈ Ps, Q.length ≤ L := fun Q hQ => h Q (by simp [hQ])
      simpa only [sumWithCost, addWithCost_length] using max_le hP (ih hPs)

theorem sumWithCost_cost_le (Ps : List (List R)) (L : ℕ)
    (h : ∀ P ∈ Ps, P.length ≤ L) :
    (sumWithCost Ps).2 ≤ Ps.length * L := by
  revert h
  induction Ps with
  | nil => intro h; simp [sumWithCost]
  | cons P Ps ih =>
      intro h
      have hP : P.length ≤ L := h P (by simp)
      have hPs : ∀ Q ∈ Ps, Q.length ≤ L := fun Q hQ => h Q (by simp [hQ])
      have ha : (addWithCost P (sumWithCost Ps).1).2 ≤ L := by
        rw [addWithCost_cost]
        exact (Nat.min_le_left _ _).trans hP
      simpa only [sumWithCost, List.length_cons, Nat.add_mul, one_mul] using
        Nat.add_le_add (ih hPs) ha

theorem productWithCost_length_le (Ps : List (List R)) (L : ℕ)
    (h : ∀ P ∈ Ps, P.length ≤ L) :
    (productWithCost Ps).1.length ≤ 1 + Ps.length * L := by
  revert h
  induction Ps with
  | nil => intro h; simp [productWithCost]
  | cons P Ps ih =>
      intro h
      have hP : P.length ≤ L := h P (by simp)
      have hPs : ∀ Q ∈ Ps, Q.length ≤ L := fun Q hQ => h Q (by simp [hQ])
      have hm := mulWithCost_length_le P (productWithCost Ps).1
      have hr := ih hPs
      simp only [productWithCost, List.length_cons]
      calc
        (mulWithCost P (productWithCost Ps).1).1.length
            ≤ P.length + (productWithCost Ps).1.length := hm
        _ ≤ L + (1 + Ps.length * L) := Nat.add_le_add hP hr
        _ = 1 + (Ps.length + 1) * L := by ring

theorem productWithCost_cost_le (Ps : List (List R)) (L : ℕ)
    (h : ∀ P ∈ Ps, P.length ≤ L) :
    (productWithCost Ps).2 ≤ 2 * Ps.length * L * (1 + Ps.length * L) := by
  revert h
  induction Ps with
  | nil => intro h; simp [productWithCost]
  | cons P Ps ih =>
      intro h
      have hP : P.length ≤ L := h P (by simp)
      have hPs : ∀ Q ∈ Ps, Q.length ≤ L := fun Q hQ => h Q (by simp [hQ])
      have hr := productWithCost_length_le Ps L hPs
      have hm : (mulWithCost P (productWithCost Ps).1).2 ≤
          2 * L * (1 + Ps.length * L) :=
        (mulWithCost_cost_le _ _).trans
          (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hP) hr)
      simp only [productWithCost, List.length_cons]
      calc
        (productWithCost Ps).2 + (mulWithCost P (productWithCost Ps).1).2
            ≤ 2 * Ps.length * L * (1 + Ps.length * L) +
              2 * L * (1 + Ps.length * L) := Nat.add_le_add (ih hPs) hm
        _ = 2 * (Ps.length + 1) * L * (1 + Ps.length * L) := by ring
        _ ≤ 2 * (Ps.length + 1) * L * (1 + (Ps.length + 1) * L) :=
          Nat.mul_le_mul_left _
            (Nat.add_le_add_left (Nat.mul_le_mul_right L (Nat.le_succ Ps.length)) 1)

@[simp] theorem evalWithCost_cost (x : R) (P : List R) :
    (evalWithCost x P).2 = 2 * P.length := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      simp only [evalWithCost, ih, List.length_cons]
      omega

omit [Semiring R] in
@[simp] theorem length_truncate (D : ℕ) (P : List R) :
    (truncate D P).length = min D P.length := by simp [truncate]

omit [Semiring R] in
theorem length_truncate_le (D : ℕ) (P : List R) :
    (truncate D P).length ≤ D := by simp [length_truncate ]

omit [Semiring R] in
@[simp] theorem truncateWithCost_cost (D : ℕ) (P : List R) :
    (truncateWithCost D P).2 = 0 := rfl

theorem coeff_truncate (D : ℕ) (P : List R) (n : ℕ) :
    coeff (truncate D P) n = if n < D then coeff P n else 0 := by
  induction D generalizing P n with
  | zero => simp [truncate, coeff]
  | succ D ih =>
      cases P with
      | nil => simp [truncate, coeff]
      | cons a P =>
          cases n with
          | zero => simp [truncate, coeff]
          | succ n => simpa [truncate, coeff] using ih P n

theorem coeff_eq_zero_of_length_le (P : List R) (n : ℕ) (h : P.length ≤ n) :
    coeff P n = 0 := by
  induction P generalizing n with
  | nil => rfl
  | cons a P ih =>
      cases n with
      | zero => simp at h
      | succ n =>
          exact ih n (by simpa using h)

theorem shiftWithCost_length_le (a : R) (P : List R) :
    (shiftWithCost a P).1.length ≤ 2 * P.length := by
  induction P with
  | nil => simp [shiftWithCost]
  | cons b P ih =>
      have hm := mulWithCost_length_le [a, 1] (shiftWithCost a P).1
      simp only [List.length_cons, List.length_nil] at hm
      simp only [shiftWithCost, addWithCost_length, List.length_cons, List.length_nil]
      omega

theorem length_shift_le (a : R) (P : List R) :
    (shift a P).length ≤ 2 * P.length := shiftWithCost_length_le a P

theorem shiftWithCost_cost_le (a : R) (P : List R) :
    (shiftWithCost a P).2 ≤ 5 * P.length ^ 2 := by
  induction P with
  | nil => simp [shiftWithCost]
  | cons b P ih =>
      have hlen := shiftWithCost_length_le a P
      have hm : (mulWithCost [a, 1] (shiftWithCost a P).1).2 ≤ 8 * P.length := by
        refine (mulWithCost_cost_le _ _).trans ?_
        simp only [List.length_cons, List.length_nil]
        omega
      have ha : (addWithCost [b] (mulWithCost [a, 1] (shiftWithCost a P).1).1).2 ≤ 1 := by
        rw [addWithCost_cost]
        exact Nat.min_le_left _ _
      simp only [shiftWithCost, List.length_cons]
      calc
        (shiftWithCost a P).2 + (mulWithCost [a, 1] (shiftWithCost a P).1).2 +
            (addWithCost [b] (mulWithCost [a, 1] (shiftWithCost a P).1).1).2
            ≤ 5 * P.length ^ 2 + 8 * P.length + 1 :=
          Nat.add_le_add (Nat.add_le_add ih hm) ha
        _ ≤ 5 * P.length ^ 2 + 10 * P.length + 5 := by omega
        _ = 5 * (P.length + 1) ^ 2 := by ring

end Algorithms

section Semantics

variable [CommSemiring R]

/-- Mathematical meaning of a coefficient list; only this interpretation is
noncomputable. The list algorithms above use no classical choice. -/
noncomputable def denote : List R → Polynomial R
  | [] => 0
  | a :: P => Polynomial.C a + Polynomial.X * denote P

@[simp] theorem denote_nil : denote ([] : List R) = 0 := rfl

@[simp] theorem denote_cons (a : R) (P : List R) :
    denote (a :: P) = Polynomial.C a + Polynomial.X * denote P := rfl

@[simp] theorem coeff_denote (P : List R) (n : ℕ) :
    (denote P).coeff n = coeff P n := by
  induction P generalizing n with
  | nil => simp [denote, coeff]
  | cons a P ih =>
      cases n with
      | zero => simp [denote, coeff]
      | succ n =>
          simp [denote, coeff, Polynomial.coeff_X_mul, ih]

theorem degree_denote_lt_length (P : List R) :
    (denote P).degree < (P.length : ℕ) := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).2
  intro n hn
  rw [coeff_denote]
  exact coeff_eq_zero_of_length_le P n hn

@[simp] theorem denote_addWithCost (P Q : List R) :
    denote (addWithCost P Q).1 = denote P + denote Q := by
  induction P generalizing Q with
  | nil => simp [addWithCost]
  | cons a P ih =>
      cases Q with
      | nil => simp [addWithCost]
      | cons b Q =>
          simp only [addWithCost, denote_cons, ih, map_add]
          ring

@[simp] theorem denote_add (P Q : List R) :
    denote (add P Q) = denote P + denote Q := denote_addWithCost P Q

@[simp] theorem denote_scaleWithCost (a : R) (P : List R) :
    denote (scaleWithCost a P).1 = Polynomial.C a * denote P := by
  induction P with
  | nil => simp [scaleWithCost]
  | cons b P ih =>
      simp only [scaleWithCost, denote_cons, ih, map_mul]
      ring

@[simp] theorem denote_scale (a : R) (P : List R) :
    denote (scale a P) = Polynomial.C a * denote P := denote_scaleWithCost a P

@[simp] theorem denote_mulWithCost (P Q : List R) :
    denote (mulWithCost P Q).1 = denote P * denote Q := by
  induction P with
  | nil => simp [mulWithCost]
  | cons a P ih =>
      simp only [mulWithCost, denote_addWithCost, denote_scaleWithCost,
        denote_cons, ih, map_zero, zero_add]
      ring

@[simp] theorem denote_mul (P Q : List R) :
    denote (mul P Q) = denote P * denote Q := denote_mulWithCost P Q

@[simp] theorem denote_sumWithCost (Ps : List (List R)) :
    denote (sumWithCost Ps).1 = (Ps.map denote).sum := by
  induction Ps with
  | nil => simp [sumWithCost]
  | cons P Ps ih => simp [sumWithCost, ih]

@[simp] theorem denote_sum (Ps : List (List R)) :
    denote (sum Ps) = (Ps.map denote).sum := denote_sumWithCost Ps

@[simp] theorem denote_productWithCost (Ps : List (List R)) :
    denote (productWithCost Ps).1 = (Ps.map denote).prod := by
  induction Ps with
  | nil => simp [productWithCost, denote]
  | cons P Ps ih => simp [productWithCost, ih]

@[simp] theorem denote_product (Ps : List (List R)) :
    denote (product Ps) = (Ps.map denote).prod := denote_productWithCost Ps

@[simp] theorem evalWithCost_value (x : R) (P : List R) :
    (evalWithCost x P).1 = (denote P).eval x := by
  induction P with
  | nil => simp [evalWithCost]
  | cons a P ih => simp [evalWithCost, ih, denote]

@[simp] theorem eval_eq (x : R) (P : List R) :
    eval x P = (denote P).eval x := evalWithCost_value x P

@[simp] theorem denote_shiftWithCost (a : R) (P : List R) :
    denote (shiftWithCost a P).1 =
      (denote P).comp (Polynomial.X + Polynomial.C a) := by
  induction P with
  | nil => simp [shiftWithCost]
  | cons b P ih =>
      simp only [shiftWithCost, denote_addWithCost, denote_mulWithCost,
        denote_cons, denote_nil, ih, map_one, mul_zero, add_zero, mul_one,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
      ring

@[simp] theorem denote_shift (a : R) (P : List R) :
    denote (shift a P) = (denote P).comp (Polynomial.X + Polynomial.C a) :=
  denote_shiftWithCost a P

theorem coeff_denote_truncate (D : ℕ) (P : List R) (n : ℕ) :
    (denote (truncate D P)).coeff n =
      if n < D then (denote P).coeff n else 0 := by
  simp only [coeff_denote, coeff_truncate]

@[simp] theorem denote_truncate (D : ℕ) (P : List R) :
    denote (truncate D P) = SubexponentialSAT.Truncation.trunc D (denote P) := by
  ext n
  simp only [coeff_denote_truncate, SubexponentialSAT.Truncation.coeff_trunc]

end Semantics

section RingOperations

variable [CommRing R]

/-- Negation through the already instrumented scalar multiplication loop. -/
def neg (P : List R) : List R := scale (-1) P

@[simp] theorem denote_neg (P : List R) :
    denote (neg P) = -denote P := by simp [neg]

end RingOperations

end SubexponentialSAT.PolynomialAlgorithm

end OAI.Algorithms
