import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramCompanion
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingBasis

namespace OAI.Algorithms

/-! Actual represented arithmetic in the quotient by a supplied monic
polynomial. Irreducibility is unnecessary for ring operations. Every structure
constant is supplied by the executable companion recurrence. -/
namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A : Type*} [CommRing A] [Nontrivial A] [DecidableEq A]

noncomputable abbrev quotientPolynomial (ops : RepresentedRing C A) {d : ℕ} (c : Code C d) :=
  SubexponentialSAT.QuarticSearch.poly (fun i => ops.decode (c i))

noncomputable abbrev Quotient (ops : RepresentedRing C A) {d : ℕ} (c : Code C d) :=
  SubexponentialSAT.LiftRing.Extension (quotientPolynomial ops c)

def zeroVector (ops : RingProgram C) (d : ℕ) : Code C d := fun _ => ops.zeroRun.1

theorem quotient_table_correct (ops : RepresentedRing C A) {d : ℕ} (hd : 0 < d)
    (c : Code C d) (i j : Fin d) :
    RingBasis.basis (quotientPolynomial ops c) i * RingBasis.basis (quotientPolynomial ops c) j =
      ∑ k, SubexponentialSAT.LiftRing.of (quotientPolynomial ops c)
        (ops.decode ((structureTableRun ops.program c).1 i j k)) *
          RingBasis.basis (quotientPolynomial ops c) k := by
  rw [RingBasis.basis_mul (quotientPolynomial ops c) (SubexponentialSAT.QuarticSearch.poly_monic _)
    (SubexponentialSAT.QuarticSearch.poly_natDegree _) i j]
  apply Finset.sum_congr rfl
  intro k _
  rw [structureTableRun_remainder ops hd]
  rfl

omit [Nontrivial A] [DecidableEq A] in
theorem quotient_zero_correct (ops : RepresentedRing C A) {d : ℕ} (c : Code C d) :
    denote ops (SubexponentialSAT.LiftRing.of (quotientPolynomial ops c))
      (RingBasis.basis (quotientPolynomial ops c)) (zeroVector ops.program d) = 0 := by
  simp only [denote, zeroVector, ops.zero_correct, map_zero,
    zero_mul, Finset.sum_const_zero]

omit [DecidableEq A] in
theorem quotient_one_correct (ops : RepresentedRing C A) {d : ℕ} (hd : 0 < d)
    (c : Code C d) :
    denote ops (SubexponentialSAT.LiftRing.of (quotientPolynomial ops c))
      (RingBasis.basis (quotientPolynomial ops c)) (oneVectorRun ops.program d).1 = 1 := by
  have hc (i : Fin d) : ops.decode ((oneVectorRun ops.program d).1 i) =
      RingBasis.coordinates (quotientPolynomial ops c) (SubexponentialSAT.QuarticSearch.poly_monic _)
        (SubexponentialSAT.QuarticSearch.poly_natDegree _) 1 i := by
    rw [RingBasis.one_coordinates _ _ _ hd]
    have h := congrFun (oneVectorRun_correct ops d) i
    exact h
  unfold denote
  simp_rw [hc]
  exact RingBasis.reconstruct _ _ _ 1

/-- This is arithmetic for every supplied monic polynomial. A separate finite
irreducible search upgrades this quotient to the intended unramified ring. -/
noncomputable def quotientRing (ops : RepresentedRing C A) {d : ℕ} (hd : 0 < d)
    (c : Code C d) : RepresentedRing (Code C d) (Quotient ops c) :=
  represented ops (SubexponentialSAT.LiftRing.of (quotientPolynomial ops c))
    (RingBasis.basis (quotientPolynomial ops c)) (structureTableRun ops.program c).1
    (zeroVector ops.program d) (oneVectorRun ops.program d).1
    (quotient_table_correct ops hd c) (quotient_zero_correct ops c)
    (quotient_one_correct ops hd c)

/-- The executable program contains no polynomial-quotient or choice operation. -/
def quotientProgram (ops : RingProgram C) {d : ℕ} (c : Code C d) : RingProgram (Code C d) :=
  program ops (structureTableRun ops c).1 (zeroVector ops d) (oneVectorRun ops d).1

/-- Explicit setup phase. Its returned program retains the materialized table,
and its cost includes all scalar callback events in constructing that table. -/
def quotientProgramRun (ops : RingProgram C) {d : ℕ} (c : Code C d) :
    RingProgram (Code C d) × ℕ :=
  let table := structureTableRun ops c
  let one := oneVectorRun ops d
  (program ops table.1 (zeroVector ops d) one.1,
    table.2 + one.2 + d * ops.zeroRun.2 + d)

@[simp] theorem quotientProgramRun_value (ops : RingProgram C) {d : ℕ} (c : Code C d) :
    (quotientProgramRun ops c).1 = quotientProgram ops c := rfl

def setupEventBudget (d q : ℕ) : ℕ :=
  d * d * (d * q + 2 * d + 2 * d * companionStepBudget d q) + d * d +
    (d * q + d) + d * q + d

theorem quotientProgramRun_cost (ops : RingProgram C) {d q : ℕ}
    (hq : ProgramBudget ops q) (c : Code C d) :
    (quotientProgramRun ops c).2 ≤ setupEventBudget d q := by
  have htable := structureTableRun_cost ops hq c
  have hone := oneVectorRun_cost ops hq d
  have hzero := Nat.mul_le_mul_left d hq.zero
  dsimp only [quotientProgramRun]
  unfold setupEventBudget
  omega

theorem setupEventBudget_polynomial (d q : ℕ) :
    setupEventBudget d q ≤ 20 * (d + 1)^4 * (q + 1) := by
  unfold setupEventBudget companionStepBudget
  nlinarith [Nat.zero_le (d^4*q), Nat.zero_le (d^3*q), Nat.zero_le (d^2*q),
    Nat.zero_le (d*q), Nat.zero_le (d^4), Nat.zero_le (d^3), Nat.zero_le (d^2)]

@[simp] theorem quotientRing_program (ops : RepresentedRing C A) {d : ℕ}
    (hd : 0 < d) (c : Code C d) :
    (quotientRing ops hd c).program = quotientProgram ops.program c := rfl

theorem quotientRing_budget (ops : RepresentedRing C A) {d q : ℕ}
    (hd : 0 < d) (hq : ScalarBudget ops q) (c : Code C d) :
    ScalarBudget (quotientRing ops hd c) (eventBudget d q) :=
  represented_budget ops _ hq _ _ _ _ _ _ _

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
