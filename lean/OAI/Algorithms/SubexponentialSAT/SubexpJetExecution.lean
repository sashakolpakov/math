import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpExecution
import OAI.Algorithms.SubexponentialSAT.SubexpTableInterpolation

namespace OAI.Algorithms

/-!
# Executing all moments and extracting the jet over code words

All scalar arithmetic uses the supplied executable RingProgram. The decoder
appears only in proofs. The returned counter accumulates every backend callback
and the expression/list-operation counters; outer map bookkeeping and the
generation of exponent/index lists still require their separate loop costs in
a primitive-machine implementation.
-/

namespace SubexponentialSAT.SubexpJetExecution

open SymbolicCost SubexpSymbolicCost SubexpExecution
open SubexpTableInterpolation (mapWithCost mapWithCost_value mapWithCost_length
  mapWithCost_cost_le)

variable {D : ℕ} {C : Type*}

def collect (ops : RingProgram C) (P : CoeffList D C) : List (RawIndex D) → C × ℕ
  | [] => ops.zeroRun
  | a :: rest =>
      let first := programScan ops P a
      let tail := collect ops P rest
      let total := ops.addRun first.1 tail.1
      (total.1, first.2 + tail.2 + total.2)

abbrev Moment (D : ℕ) (C : Type*) := (Fin D → ℕ) × CoeffList D C

def finishAt (ops : RingProgram C) (r : ℕ) : List (Moment D C) → C × ℕ
  | [] => ops.zeroRun
  | m :: ms =>
      let current := collect ops m.2 ((List.range (D + 1)).map fun j => (m.1, (j, r)))
      let rest := finishAt ops r ms
      let total := ops.addRun current.1 rest.1
      (total.1, current.2 + rest.2 + total.2)

def finish (ops : RingProgram C) (ms : List (Moment D C)) : List C × ℕ :=
  mapWithCost (fun r => finishAt ops r ms) (List.range D)

def moments (ops : RingProgram C)
    (program : (Fin D → ℕ) → Algorithm.Expr (CoeffList D C)) :
    List (Moment D C) × ℕ :=
  mapWithCost (fun a =>
    let out := programEval ops (Algorithm.retainedSlots D) (program a)
    ((a, out.1), out.2)) (Algorithm.exponentList D (2 * D + 1))

/-- The finite code-word jet evaluator, including each retained moment once. -/
def executeJet (ops : RingProgram C)
    (program : (Fin D → ℕ) → Algorithm.Expr (CoeffList D C)) : List C × ℕ :=
  let ms := moments ops program
  let out := finish ops ms.1
  (out.1, ms.2 + out.2)

@[simp] theorem moments_length (ops : RingProgram C)
    (program : (Fin D → ℕ) → Algorithm.Expr (CoeffList D C)) :
    (moments ops program).1.length = (3 * D + 1).choose D := by
  simp only [moments, mapWithCost_length, Algorithm.exponentList_length]
  congr 1
  omega

theorem moments_dense (ops : RingProgram C)
    (program : (Fin D → ℕ) → Algorithm.Expr (CoeffList D C))
    (m : Moment D C) (hm : m ∈ (moments ops program).1) :
    m.2.length = (Algorithm.retainedSlots D).length := by
  simp only [moments, mapWithCost_value] at hm
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
  exact programEval_length _ _ _

@[simp] theorem executeJet_length (ops : RingProgram C)
    (program : (Fin D → ℕ) → Algorithm.Expr (CoeffList D C)) :
    (executeJet ops program).1.length = D := by
  simp [executeJet, finish]

section Decode

variable {R : Type*} [CommRing R] (ops : RepresentedRing C R)

theorem collect_decode (P : CoeffList D C) (indices : List (RawIndex D)) :
    ops.decode (collect ops.program P indices).1 =
      (indices.map (coeff (decodeList ops P))).sum := by
  induction indices with
  | nil => exact ops.zero_correct
  | cons a rest ih =>
      change ops.decode (ops.addRun _ _).1 = _
      rw [ops.add_correct]
      simp only [programScan_represented, representedScan_correct, ih,
        List.map_cons, List.sum_cons]

theorem finishAt_decode (r : ℕ) (ms : List (Moment D C)) :
    ops.decode (finishAt ops.program r ms).1 =
      (ms.map fun m => Algorithm.collapseU m.1 r (decodeList ops m.2)).sum := by
  induction ms with
  | nil => exact ops.zero_correct
  | cons m ms ih =>
      change ops.decode (ops.addRun _ _).1 = _
      rw [ops.add_correct, collect_decode, ih]
      simp only [List.map_cons, List.sum_cons, Algorithm.collapseU_eq,
        List.map_map, Function.comp_def]

theorem finish_decode (ms : List (Moment D C)) :
    (finish ops.program ms).1.map ops.decode =
      (List.range D).map fun r =>
        (ms.map fun m => Algorithm.collapseU m.1 r (decodeList ops m.2)).sum := by
  simp only [finish, mapWithCost_value, List.map_map, Function.comp_def, finishAt_decode]

private theorem map_map {L S T : Type*} (f : L → S) (g : S → T) (e : Algorithm.Expr L) :
    (e.map f).map g = e.map (fun x => g (f x)) := by
  induction e with
  | lit x => rfl
  | add e f he hf => simp [Algorithm.Expr.map, he, hf]
  | mul e f he hf => simp [Algorithm.Expr.map, he, hf]

/-- The entire word-code algorithm refines the previously proved raw jet
algorithm. No algebraic laws on code words are assumed. -/
theorem executeJet_decode
    (program : (Fin D → ℕ) → Algorithm.Expr (CoeffList D C)) :
    (executeJet ops.program program).1.map ops.decode =
      Algorithm.executeRawJet (fun a => (program a).map (decodeList ops)) := by
  change (finish ops.program (moments ops.program program).1).1.map ops.decode = _
  rw [finish_decode, Algorithm.executeRawJet, Algorithm.executeJet_eq]
  simp only [moments, mapWithCost_value, List.map_map, Function.comp_def,
    programEval_decode, map_map]

end Decode

section Costs

variable {R : Type*} [CommRing R] (ops : RepresentedRing C R)
variable {q : ℕ} (budget : ScalarBudget ops q)

include budget

theorem collect_cost (P : CoeffList D C) (indices : List (RawIndex D)) :
    (collect ops.program P indices).2 ≤
      indices.length * ((q + 2) * P.length + 2 * q) + q := by
  induction indices with
  | nil => simpa [collect] using budget.zero
  | cons a rest ih =>
      have hs := representedScan_cost ops budget P a
      have ha := budget.add (programScan ops.program P a).1 (collect ops.program P rest).1
      change (programScan ops.program P a).2 + (collect ops.program P rest).2 +
        (ops.addRun _ _).2 ≤ _
      rw [programScan_represented]
      rw [programScan_represented] at ha
      calc
        _ ≤ ((q + 2) * P.length + q) +
            (rest.length * ((q + 2) * P.length + 2 * q) + q) + q :=
          Nat.add_le_add (Nat.add_le_add hs ih) ha
        _ = _ := by simp only [List.length_cons]; ring

theorem finishAt_cost (r N : ℕ) (ms : List (Moment D C))
    (hlen : ∀ m ∈ ms, m.2.length = N) :
    (finishAt ops.program r ms).2 ≤
      ms.length * ((D + 1) * ((q + 2) * N + 2 * q) + 2 * q) + q := by
  induction ms with
  | nil => simpa [finishAt] using budget.zero
  | cons m ms ih =>
      have hm := hlen m (by simp)
      have hi := ih (fun t ht => hlen t (by simp [ht]))
      have hc := collect_cost ops budget m.2
        ((List.range (D + 1)).map fun j => (m.1, (j, r)))
      simp only [List.length_map, List.length_range, hm] at hc
      have ha := budget.add
        (collect ops.program m.2 ((List.range (D + 1)).map fun j => (m.1, (j, r)))).1
        (finishAt ops.program r ms).1
      change (collect ops.program m.2 _).2 + (finishAt ops.program r ms).2 +
        (ops.addRun _ _).2 ≤ _
      calc
        _ ≤ ((D + 1) * ((q + 2) * N + 2 * q) + q) +
            (ms.length * ((D + 1) * ((q + 2) * N + 2 * q) + 2 * q) + q) + q :=
          Nat.add_le_add (Nat.add_le_add hc hi) ha
        _ = _ := by simp only [List.length_cons]; ring

theorem executeJet_cost
    (program : (Fin D → ℕ) → Algorithm.Expr (CoeffList D C)) (maxRaw S : ℕ)
    (hraw : ∀ a ∈ Algorithm.exponentList D (2 * D + 1),
      EveryLiteral (fun raw => raw.length ≤ maxRaw) (program a))
    (hsize : ∀ a ∈ Algorithm.exponentList D (2 * D + 1), (program a).size ≤ S) :
    (executeJet ops.program program).2 ≤
      ((3 * D + 1).choose D) *
        (SubexpExecution.instructionBudget (Algorithm.retainedSlots D).length maxRaw q * S) +
      D * (((3 * D + 1).choose D) *
        ((D + 1) * ((q + 2) * (Algorithm.retainedSlots D).length + 2 * q) + 2 * q) + q) := by
  have hm := mapWithCost_cost_le (fun a =>
      let out := programEval ops.program (Algorithm.retainedSlots D) (program a)
      ((a, out.1), out.2)) (Algorithm.exponentList D (2 * D + 1))
      (SubexpExecution.instructionBudget (Algorithm.retainedSlots D).length maxRaw q * S)
      (by
        intro a ha
        exact (programEval_cost ops budget _ maxRaw (program a) (hraw a ha)).trans
          (Nat.mul_le_mul_left _ (hsize a ha)))
  rw [Algorithm.exponentList_length] at hm
  have he : D + (2 * D + 1) = 3 * D + 1 := by omega
  rw [he] at hm
  have hf := mapWithCost_cost_le
      (fun r => finishAt ops.program r (moments ops.program program).1) (List.range D)
      (((3 * D + 1).choose D) *
        ((D + 1) * ((q + 2) * (Algorithm.retainedSlots D).length + 2 * q) + 2 * q) + q)
      (by
        intro r hr
        simpa only [moments_length] using
          finishAt_cost ops budget r (Algorithm.retainedSlots D).length
            (moments ops.program program).1 (moments_dense ops.program program))
  simp only [List.length_range] at hf
  exact Nat.add_le_add hm hf

end Costs

end SubexponentialSAT.SubexpJetExecution

end OAI.Algorithms
