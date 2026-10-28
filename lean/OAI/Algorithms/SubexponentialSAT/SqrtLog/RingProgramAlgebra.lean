import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A R : Type*} [CommRing A] [CommRing R]

/-- A coefficient vector interpreted in a supplied finite basis. -/
def denote (ops : RepresentedRing C A) (scalar : A →+* R)
    {d : ℕ} (basis : Fin d → R) (x : Code C d) : R :=
  ∑ i, scalar (ops.decode (x i)) * basis i

theorem denote_add (ops : RepresentedRing C A) (scalar : A →+* R)
    {d : ℕ} (basis : Fin d → R) (x y : Code C d) :
    denote ops scalar basis (addRun ops.program x y).1 =
      denote ops scalar basis x + denote ops scalar basis y := by
  simp only [denote, addRun, tabulateRun, List.Vector.get_ofFn, ops.add_correct,
    map_add, add_mul, Finset.sum_add_distrib]

theorem denote_neg (ops : RepresentedRing C A) (scalar : A →+* R)
    {d : ℕ} (basis : Fin d → R) (x : Code C d) :
    denote ops scalar basis (negRun ops.program x).1 = -denote ops scalar basis x := by
  simp only [denote, negRun, tabulateRun, List.Vector.get_ofFn, ops.neg_correct,
    map_neg, neg_mul, Finset.sum_neg_distrib]

theorem denote_mul (ops : RepresentedRing C A) (scalar : A →+* R)
    {d : ℕ} (basis : Fin d → R) (table : Fin d → Fin d → Fin d → C)
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (ops.decode (table i j k)) * basis k) (x y : Code C d) :
    denote ops scalar basis (mulRun ops.program table x y).1 =
      denote ops scalar basis x * denote ops scalar basis y := by
  conv_lhs => simp only [denote, mulRun, tabulateRun_eq]
  simp_rw [coordinateMulRun_correct, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d)))
    (t := (Finset.univ : Finset (Fin d))) (f := fun k j =>
      scalar (ops.decode (x _)) * scalar (ops.decode (y j)) *
        scalar (ops.decode (table _ j k)) * basis k)]
  simp_rw [mul_assoc, ← Finset.mul_sum, ← htable]
  simp only [denote, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- One bound covering every coefficient-vector callback. -/
def eventBudget (d q : ℕ) : ℕ := d * (q + d * d * (3 * q + 1)) + d

/-- Constants are supplied cached coefficient vectors, not semantic encodings
computed by this callback. Copying a constant charges its coefficient count. -/
def program (ops : RingProgram C) {d : ℕ}
    (table : Fin d → Fin d → Fin d → C) (zero one : Code C d) :
    RingProgram (Code C d) where
  zeroRun := (zero, d)
  oneRun := (one, d)
  addRun := addRun ops
  mulRun := mulRun ops table
  negRun := negRun ops

def represented (ops : RepresentedRing C A) (scalar : A →+* R)
    {d : ℕ} (basis : Fin d → R) (table : Fin d → Fin d → Fin d → C)
    (zero one : Code C d)
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (ops.decode (table i j k)) * basis k)
    (hzero : denote ops scalar basis zero = 0)
    (hone : denote ops scalar basis one = 1) : RepresentedRing (Code C d) R where
  decode := denote ops scalar basis
  zeroRun := (zero, d)
  oneRun := (one, d)
  addRun := addRun ops.program
  mulRun := mulRun ops.program table
  negRun := negRun ops.program
  zero_correct := hzero
  one_correct := hone
  add_correct := denote_add ops scalar basis
  mul_correct := denote_mul ops scalar basis table htable
  neg_correct := denote_neg ops scalar basis

@[simp] theorem represented_program (ops : RepresentedRing C A) (scalar : A →+* R)
    {d : ℕ} (basis : Fin d → R) (table : Fin d → Fin d → Fin d → C)
    (zero one : Code C d) (htable hzero hone) :
    (represented ops scalar basis table zero one htable hzero hone).program =
      program ops.program table zero one := rfl

theorem program_budget (ops : RingProgram C) {d q : ℕ} (hq : ProgramBudget ops q)
    (table : Fin d → Fin d → Fin d → C) (zero one : Code C d) :
    ProgramBudget (program ops table zero one) (eventBudget d q) := by
  have hsmall : d * q + d ≤ eventBudget d q := by
    unfold eventBudget
    nlinarith [Nat.zero_le (d * d * (3 * q + 1))]
  constructor
  · change d ≤ eventBudget d q
    exact (Nat.le_add_left d (d * q)).trans hsmall
  · change d ≤ eventBudget d q
    exact (Nat.le_add_left d (d * q)).trans hsmall
  · intro x y
    exact (addRun_cost ops hq x y).trans hsmall
  · intro x y
    exact mulRun_cost ops hq table x y
  · intro x
    exact (negRun_cost ops hq x).trans hsmall

theorem eventBudget_polynomial (d q : ℕ) :
    eventBudget d q ≤ (d + 1)^3 * (3 * q + 2) := by
  unfold eventBudget
  nlinarith [Nat.zero_le (d * d), Nat.zero_le (d * q), Nat.zero_le (d * d * q)]

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
