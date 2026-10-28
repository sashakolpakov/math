import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost

namespace OAI.Algorithms

/-!
# Dynamic-degree coefficient arithmetic

These executable callbacks operate on a runtime-sized coefficient vector.
Their counters include all scalar callbacks and one event per vector/list
entry. A separate flat-stack refinement must account for scanning serialized
vectors; callback event counts alone are not claimed to be primitive time.
-/
namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A : Type*} [CommRing A]

/-- Evaluate and sum a list of measured scalar computations. -/
def sumRun (ops : RingProgram C) : List (C × ℕ) → C × ℕ
  | [] => ops.zeroRun
  | x :: xs =>
    let s := sumRun ops xs
    let out := ops.addRun x.1 s.1
    (out.1, x.2 + s.2 + out.2 + 1)

theorem sumRun_correct (ops : RepresentedRing C A) (xs : List (C × ℕ)) :
    ops.decode (sumRun ops.program xs).1 = (xs.map fun x => ops.decode x.1).sum := by
  induction xs with
  | nil => exact ops.zero_correct
  | cons x xs ih =>
    change ops.decode (ops.addRun x.1 (sumRun ops.program xs).1).1 = _
    rw [ops.add_correct, ih]
    rfl

theorem sumRun_cost (ops : RingProgram C) {q a : ℕ} (hq : ProgramBudget ops q)
    (xs : List (C × ℕ)) (hx : ∀ x ∈ xs, x.2 ≤ a) :
    (sumRun ops xs).2 ≤ q + xs.length * (a + q + 1) := by
  induction xs with
  | nil => simpa only [sumRun, List.length_nil, Nat.zero_mul, Nat.add_zero] using hq.zero
  | cons x xs ih =>
    have hxs := ih (fun y hy => hx y (List.mem_cons_of_mem x hy))
    have hxx := hx x (List.mem_cons_self)
    have hadd := hq.add x.1 (sumRun ops xs).1
    simp only [sumRun, List.length_cons]
    nlinarith

/-- Tabulation explicitly charges one event per output coefficient. -/
def tabulateRun {d : ℕ} (f : Fin d → C × ℕ) : (Fin d → C) × ℕ :=
  let stored := List.Vector.ofFn f
  (fun i => (stored.get i).1, (∑ i, (stored.get i).2) + d)

@[simp] theorem tabulateRun_eq {d : ℕ} (f : Fin d → C × ℕ) :
    tabulateRun f = (fun i => (f i).1, (∑ i, (f i).2) + d) := by
  simp only [tabulateRun, List.Vector.get_ofFn]

theorem tabulateRun_cost {d a : ℕ} (f : Fin d → C × ℕ)
    (hf : ∀ i, (f i).2 ≤ a) :
    (tabulateRun f).2 ≤ d * a + d := by
  have hs : (∑ i, (f i).2) ≤ ∑ _i : Fin d, a := Finset.sum_le_sum (fun i _ => hf i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    tabulateRun, List.Vector.get_ofFn] using Nat.add_le_add_right hs d

abbrev Code (C : Type*) (d : ℕ) := Fin d → C

def addRun (ops : RingProgram C) {d : ℕ} (x y : Code C d) : Code C d × ℕ :=
  tabulateRun fun i => ops.addRun (x i) (y i)

def negRun (ops : RingProgram C) {d : ℕ} (x : Code C d) : Code C d × ℕ :=
  tabulateRun fun i => ops.negRun (x i)

/-- Two scalar multiplications, with both measured costs retained. -/
def tripleRun (ops : RingProgram C) (a b c : C) : C × ℕ :=
  let ab := ops.mulRun a b
  let abc := ops.mulRun ab.1 c
  (abc.1, ab.2 + abc.2)

def coordinateMulRun (ops : RingProgram C) {d : ℕ}
    (table : Fin d → Fin d → Fin d → C) (x y : Code C d) (k : Fin d) : C × ℕ :=
  sumRun ops ((List.ofFn fun i : Fin d =>
    List.ofFn fun j : Fin d => tripleRun ops (x i) (y j) (table i j k)).flatten)

def mulRun (ops : RingProgram C) {d : ℕ}
    (table : Fin d → Fin d → Fin d → C) (x y : Code C d) : Code C d × ℕ :=
  tabulateRun fun k => coordinateMulRun ops table x y k

@[simp] theorem tripleRun_correct (ops : RepresentedRing C A) (a b c : C) :
    ops.decode (tripleRun ops.program a b c).1 =
      ops.decode a * ops.decode b * ops.decode c := by
  simp only [tripleRun, ops.mul_correct]

theorem coordinateMulRun_correct (ops : RepresentedRing C A) {d : ℕ}
    (table : Fin d → Fin d → Fin d → C) (x y : Code C d) (k : Fin d) :
    ops.decode (coordinateMulRun ops.program table x y k).1 =
      ∑ i, ∑ j, ops.decode (x i) * ops.decode (y j) * ops.decode (table i j k) := by
  rw [coordinateMulRun, sumRun_correct]
  simp [List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn]

theorem coordinateMulRun_cost (ops : RingProgram C) {q d : ℕ}
    (hq : ProgramBudget ops q) (table : Fin d → Fin d → Fin d → C)
    (x y : Code C d) (k : Fin d) :
    (coordinateMulRun ops table x y k).2 ≤ q + d * d * (3 * q + 1) := by
  have hterm (i j : Fin d) : (tripleRun ops (x i) (y j) (table i j k)).2 ≤ 2 * q := by
    have h₁ := hq.mul (x i) (y j)
    have h₂ := hq.mul (ops.mulRun (x i) (y j)).1 (table i j k)
    simp only [tripleRun]
    omega
  unfold coordinateMulRun
  have h := sumRun_cost ops hq
    ((List.ofFn fun i : Fin d =>
      List.ofFn fun j : Fin d => tripleRun ops (x i) (y j) (table i j k)).flatten)
    (a := 2 * q) (by
      intro z hz
      obtain ⟨ys, hys, hzy⟩ := List.mem_flatten.mp hz
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hys
      rw [← hi] at hzy
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hzy
      rw [← hj]
      exact hterm i j)
  simpa [List.length_flatten, List.map_ofFn, List.sum_ofFn, Nat.mul_assoc,
    show 2 * q + q + 1 = 3 * q + 1 by omega] using h

theorem mulRun_cost (ops : RingProgram C) {q d : ℕ}
    (hq : ProgramBudget ops q) (table : Fin d → Fin d → Fin d → C)
    (x y : Code C d) :
    (mulRun ops table x y).2 ≤ d * (q + d * d * (3 * q + 1)) + d :=
  tabulateRun_cost _ (coordinateMulRun_cost ops hq table x y)

theorem addRun_cost (ops : RingProgram C) {q d : ℕ}
    (hq : ProgramBudget ops q) (x y : Code C d) :
    (addRun ops x y).2 ≤ d * q + d :=
  tabulateRun_cost _ (fun i => hq.add (x i) (y i))

theorem negRun_cost (ops : RingProgram C) {q d : ℕ}
    (hq : ProgramBudget ops q) (x : Code C d) :
    (negRun ops x).2 ≤ d * q + d :=
  tabulateRun_cost _ (fun i => hq.neg (x i))

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
