import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramSerialization

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A : Type*} [CommRing A]

abbrev Triple (C : Type*) := C × C × C

def dotTriplesRun (ops : RingProgram C) (xs : List (Triple C)) : C × ℕ :=
  sumRun ops (xs.map fun x => tripleRun ops x.1 x.2.1 x.2.2)

def accumulateTriplesRun (ops : RingProgram C) : List (Triple C) → C → C × ℕ
  | [], z => (z, 0)
  | x :: xs, z =>
    let term := tripleRun ops x.1 x.2.1 x.2.2
    let s := ops.addRun z term.1
    let out := accumulateTriplesRun ops xs s.1
    (out.1, term.2 + s.2 + out.2 + 1)

def tripleValue (ops : RepresentedRing C A) (x : Triple C) : A :=
  ops.decode x.1 * ops.decode x.2.1 * ops.decode x.2.2

theorem dotTriplesRun_correct (ops : RepresentedRing C A) (xs : List (Triple C)) :
    ops.decode (dotTriplesRun ops.program xs).1 = (xs.map (tripleValue ops)).sum := by
  rw [dotTriplesRun, sumRun_correct]
  simp only [List.map_map, Function.comp_def, tripleRun_correct ]
  rfl

theorem accumulateTriplesRun_correct (ops : RepresentedRing C A)
    (xs : List (Triple C)) (z : C) :
    ops.decode (accumulateTriplesRun ops.program xs z).1 =
      ops.decode z + (xs.map (tripleValue ops)).sum := by
  induction xs generalizing z with
  | nil => simp [accumulateTriplesRun]
  | cons x xs ih =>
    change ops.decode (accumulateTriplesRun ops.program xs
      (ops.addRun z (tripleRun ops.program x.1 x.2.1 x.2.2).1).1).1 = _
    rw [ih, ops.add_correct, tripleRun_correct]
    simp only [List.map_cons, List.sum_cons, tripleValue]
    ring

theorem tripleRun_cost (ops : RingProgram C) {q : ℕ} (hq : ProgramBudget ops q)
    (a b c : C) : (tripleRun ops a b c).2 ≤ 2*q := by
  have hab := hq.mul a b
  have habc := hq.mul (ops.mulRun a b).1 c
  simp only [tripleRun]
  omega

theorem accumulateTriplesRun_cost (ops : RingProgram C) {q : ℕ}
    (hq : ProgramBudget ops q) (xs : List (Triple C)) (z : C) :
    (accumulateTriplesRun ops xs z).2 ≤ xs.length * (3*q+1) := by
  induction xs generalizing z with
  | nil => simp [accumulateTriplesRun]
  | cons x xs ih =>
    have ht := tripleRun_cost ops hq x.1 x.2.1 x.2.2
    have ha := hq.add z (tripleRun ops x.1 x.2.1 x.2.2).1
    have hi := ih (ops.addRun z (tripleRun ops x.1 x.2.1 x.2.2).1).1
    simp only [accumulateTriplesRun, List.length_cons]
    nlinarith

theorem dotTriplesRun_cost (ops : RingProgram C) {q : ℕ}
    (hq : ProgramBudget ops q) (xs : List (Triple C)) :
    (dotTriplesRun ops xs).2 ≤ q + xs.length * (3*q+1) := by
  unfold dotTriplesRun
  have h := sumRun_cost ops hq (xs.map fun x => tripleRun ops x.1 x.2.1 x.2.2)
    (a := 2*q) (by
      intro x hx
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      exact tripleRun_cost ops hq y.1 y.2.1 y.2.2)
  simpa only [List.length_map, show 2*q+q+1=3*q+1 by omega] using h

def coordinateTriples {d : ℕ} (table : Fin d → Fin d → Fin d → C)
    (x y : Code C d) (k : Fin d) : List (Triple C) :=
  (List.ofFn fun i : Fin d => List.ofFn fun j : Fin d => (x i, y j, table i j k)).flatten

@[simp] theorem coordinateTriples_length {d : ℕ}
    (table : Fin d → Fin d → Fin d → C) (x y : Code C d) (k : Fin d) :
    (coordinateTriples table x y k).length = d * d := by
  simp [coordinateTriples, List.length_flatten, List.map_ofFn, List.sum_ofFn]

theorem coordinateMulRun_eq_dot (ops : RingProgram C) {d : ℕ}
    (table : Fin d → Fin d → Fin d → C) (x y : Code C d) (k : Fin d) :
    coordinateMulRun ops table x y k = dotTriplesRun ops (coordinateTriples table x y k) := by
  simp [coordinateMulRun, dotTriplesRun, coordinateTriples, List.map_flatten,
    List.map_ofFn, Function.comp_def]

section Words

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

variable (p t : ℕ) [Fact p.Prime]
variable (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t) (cache : ScalarCache p t)

theorem accumulateTriplesRun_canonical (xs : List (Triple (ScalarCode p t)))
    (z : ScalarCode p t) (hz : BinaryArithmetic.toNat z.val < p^t) :
    BinaryArithmetic.toNat (accumulateTriplesRun (scalarProgram p t M cache) xs z).1.val < p^t := by
  induction xs generalizing z with
  | nil => exact hz
  | cons x xs ih =>
    apply ih
    exact SubexponentialSAT.SubexpPreparedQuartic.wordAdd_canonical p t M _ _

theorem dotTriplesRun_canonical (xs : List (Triple (ScalarCode p t)))
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) :
    BinaryArithmetic.toNat (dotTriplesRun (scalarProgram p t M cache) xs).1.val < p^t := by
  cases xs with
  | nil => exact hz
  | cons x xs => exact sumRun_canonical p t M cache _ _

/-- A left-to-right streaming accumulator agrees byte-for-byte with the
callback's right-associated sum, not only after semantic decoding. -/
theorem accumulateTriplesRun_eq_dot (xs : List (Triple (ScalarCode p t)))
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) :
    (accumulateTriplesRun (scalarProgram p t M cache) xs cache.zero).1 =
      (dotTriplesRun (scalarProgram p t M cache) xs).1 := by
  apply word_eq_of_value p t
  · exact accumulateTriplesRun_canonical p t M cache xs cache.zero hz
  · exact dotTriplesRun_canonical p t M cache xs hz
  · have ha := accumulateTriplesRun_correct (scalarRing p t M cache) xs cache.zero
    have hd := dotTriplesRun_correct (scalarRing p t M cache) xs
    change wordValue p t _ = wordValue p t _
    change wordValue p t _ = wordValue p t cache.zero + _ at ha
    rw [cache.zero_correct, zero_add] at ha
    exact ha.trans hd.symm

/-- Reordering the emitted triples does not change the canonical output word. -/
theorem dotTriplesRun_eq_of_perm {xs ys : List (Triple (ScalarCode p t))}
    (hperm : xs.Perm ys) (hz : BinaryArithmetic.toNat cache.zero.val < p^t) :
    (dotTriplesRun (scalarProgram p t M cache) xs).1 =
      (dotTriplesRun (scalarProgram p t M cache) ys).1 := by
  apply word_eq_of_value p t
  · exact dotTriplesRun_canonical p t M cache xs hz
  · exact dotTriplesRun_canonical p t M cache ys hz
  · have hx := dotTriplesRun_correct (scalarRing p t M cache) xs
    have hy := dotTriplesRun_correct (scalarRing p t M cache) ys
    exact hx.trans ((hperm.map (tripleValue (scalarRing p t M cache))).sum_eq.trans hy.symm)

end Words
end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
