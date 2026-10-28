import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTableInterpolation
import OAI.Algorithms.SubexponentialSAT.SubexpDensePolynomial
import OAI.Algorithms.SubexponentialSAT.SubexpResidueInverse

namespace OAI.Algorithms

/-!
# Table-cache preprocessing through concrete coefficient callbacks

Every scalar operation, including denominator construction, invokes the shared
represented-ring implementation. Returned counters are accumulated by actual
finite loops. The bounds remain explicit in p, precision, and callback cost.
-/

namespace SubexponentialSAT.SubexpTableExecution

open SubexpTableInterpolation

variable {C R : Type*} [CommRing R] (ops : SubexpSymbolicCost.RepresentedRing C R)
variable {p : ℕ}

def factorRun (v d : Fin p → C) (i j : Fin p) : List C × ℕ :=
  if i = j then ([ops.oneRun.1], ops.oneRun.2) else
    let product := ops.mulRun (d j) (v j)
    let negative := ops.negRun product.1
    ([negative.1, d j], product.2 + negative.2)

def basisRun (v d : Fin p → C) (i : Fin p) : List C × ℕ :=
  let factors := mapWithCost (factorRun ops v d i) (List.finRange p)
  let result := SubexpDensePolynomial.productRun ops factors.1
  (result.1, factors.2 + result.2)

def cacheRun (v : Fin p → C) (d : Fin p → Fin p → C) : List (List C) × ℕ :=
  mapWithCost (fun i => basisRun ops v (d i) i) (List.finRange p)

theorem factorRun_length (v d : Fin p → C) (i j : Fin p) :
    (factorRun ops v d i j).1.length ≤ 2 := by
  unfold factorRun
  split <;> simp

theorem factorRun_decode (v d : Fin p → C) (i j : Fin p) :
    SubexpDensePolynomial.decodeList ops (factorRun ops v d i j).1 =
      (factorWithCost (fun k => ops.decode (v k)) (fun k => ops.decode (d k)) i j).1 := by
  unfold factorRun factorWithCost
  split <;> simp [SubexpDensePolynomial.decodeList, ops.one_correct,
    ops.mul_correct, ops.neg_correct]

theorem basisRun_decode (v d : Fin p → C) (i : Fin p) :
    SubexpDensePolynomial.decodeList ops (basisRun ops v d i).1 =
      (basisWithCost (fun k => ops.decode (v k)) (fun k => ops.decode (d k)) i).1 := by
  change SubexpDensePolynomial.decodeList ops (SubexpDensePolynomial.productRun ops _).1 = _
  rw [SubexpDensePolynomial.productRun_correct]
  simp only [basisWithCost, mapWithCost_value, List.map_map, Function.comp_def,
    factorRun_decode]
  rfl

theorem basisRun_length (v d : Fin p → C) (i : Fin p) :
    (basisRun ops v d i).1.length ≤ 1 + 2 * p := by
  rw [← SubexpDensePolynomial.decodeList_length ops, basisRun_decode]
  exact basisWithCost_length _ _ _

@[simp] theorem cacheRun_length (v : Fin p → C) (d : Fin p → Fin p → C) :
    (cacheRun ops v d).1.length = p := by simp [cacheRun]

theorem cacheRun_get (v : Fin p → C) (d : Fin p → Fin p → C) (i : Fin p) :
    (cacheRun ops v d).1.getD i.val [] = (basisRun ops v (d i) i).1 := by
  exact mapWithCost_getD_finRange _ i []

theorem cacheRun_get_length (v : Fin p → C) (d : Fin p → Fin p → C) (i : Fin p) :
    ((cacheRun ops v d).1.getD i.val []).length ≤ 1 + 2 * p := by
  rw [cacheRun_get]
  exact basisRun_length ops v (d i) i

theorem cacheRun_correct (v : Fin p → C) (d : Fin p → Fin p → C)
    (hu : TableInterpolation.UnitDifferences (fun k => ops.decode (v k)))
    (hd : ∀ i j, i ≠ j → ops.decode (d i j) * (ops.decode (v i) - ops.decode (v j)) = 1)
    (i : Fin p) :
    PolynomialAlgorithm.denote (SubexpDensePolynomial.decodeList ops
      ((cacheRun ops v d).1.getD i.val [])) =
        TableInterpolation.basis (fun k => ops.decode (v k)) hu i := by
  rw [cacheRun_get, basisRun_decode]
  exact basisWithCost_denote _ hu _ i (hd i)

variable {B : ℕ} (budget : SubexpSymbolicCost.ScalarBudget ops B)

include budget

theorem factorRun_cost (v d : Fin p → C) (i j : Fin p) :
    (factorRun ops v d i j).2 ≤ 2 * B := by
  unfold factorRun
  split
  · exact budget.one.trans (by omega)
  · simpa only [two_mul] using Nat.add_le_add (budget.mul _ _) (budget.neg _)

def basisCalls (p : ℕ) : ℕ := 2 * p + 1 + 6 * p * (1 + 2 * p)

theorem basisRun_cost (v d : Fin p → C) (i : Fin p) :
    (basisRun ops v d i).2 ≤ basisCalls p * B := by
  have hf := mapWithCost_cost_le (factorRun ops v d i) (List.finRange p) (2 * B)
    (fun j _ => factorRun_cost ops budget v d i j)
  have hp := SubexpDensePolynomial.productRun_cost ops budget
    (mapWithCost (factorRun ops v d i) (List.finRange p)).1 2 (by
      intro P hP
      simp only [mapWithCost_value, List.mem_map] at hP
      obtain ⟨j, _, rfl⟩ := hP
      exact factorRun_length ops v d i j)
  change _ + _ ≤ _
  have h := Nat.add_le_add hf hp
  simp only [mapWithCost_length, List.length_finRange] at h
  calc
    _ ≤ p * (2 * B) + (1 + 3 * p * 2 * (1 + p * 2)) * B := h
    _ = _ := by unfold basisCalls; ring

theorem cacheRun_cost (v : Fin p → C) (d : Fin p → Fin p → C) :
    (cacheRun ops v d).2 ≤ p * basisCalls p * B := by
  have h := mapWithCost_cost_le (fun i => basisRun ops v (d i) i) (List.finRange p)
    (basisCalls p * B) (fun i _ => basisRun_cost ops budget v (d i) i)
  simpa only [cacheRun, List.length_finRange, Nat.mul_assoc] using h

omit budget

/-- The complete callback computation caches every inverse before any basis
polynomial is formed. The integer labels are supplied in their concrete encoding. -/
def integerCacheRun (μ : ℕ) (v : Fin p → C) : List (List C) × ℕ :=
  let inverses := SubexpResidueInverse.inverseTableRun ops v p μ
  let cache := cacheRun ops v (fun i j => (inverses.1.get i).get j)
  (cache.1, inverses.2 + cache.2)

theorem integerInverse_lifted (p μ : ℕ) (hp : p.Prime) (hμ : 0 < μ)
    (φ : ZMod (p ^ μ) →+* R) (i j : Fin p) (hij : i ≠ j) :
    NilpotentDefect.geometricInverse ((i.val : R) - j.val)
      (((i.val : R) - j.val) ^ (p - 2)) μ * ((i.val : R) - j.val) = 1 := by
  have h := integerInverseWithCost_correct p μ hp hμ i j hij
  simp only [integerInverseWithCost, ite_eq_right hij, inverseWithCost_value] at h
  have hm := congrArg φ h
  simpa [NilpotentDefect.geometricInverse] using hm

theorem integerCacheRun_correct (μ : ℕ) (hp : p.Prime) (hμ : 0 < μ)
    (φ : ZMod (p ^ μ) →+* R) (v : Fin p → C)
    (hv : ∀ i, ops.decode (v i) = (i.val : R))
    (hu : TableInterpolation.UnitDifferences (fun i => ops.decode (v i))) (i : Fin p) :
    PolynomialAlgorithm.denote (SubexpDensePolynomial.decodeList ops
      ((integerCacheRun ops μ v).1.getD i.val [])) =
        TableInterpolation.basis (fun i => ops.decode (v i)) hu i := by
  apply cacheRun_correct
  intro a b hab
  rw [SubexpResidueInverse.inverseTableRun_entry, SubexpResidueInverse.differenceInverseRun_value,
    SubexpResidueInverse.differenceInverseWithCost_value _ _ _ _ _ hab,
    SubexpResidueInverse.inverseWithCost_value]
  simp only [hv]
  exact integerInverse_lifted p μ hp hμ φ a b hab

theorem encodedIntegerUnits (μ : ℕ) (hp : p.Prime)
    (φ : ZMod (p ^ μ) →+* R) (v : Fin p → C)
    (hv : ∀ i, ops.decode (v i) = (i.val : R)) :
    TableInterpolation.UnitDifferences (fun i => ops.decode (v i)) := by
  intro i j hij
  have h := ((TableInterpolation.unitDifferences_zmod_integerLabels p μ hp).map φ) i j hij
  change IsUnit (φ (i.val : ZMod (p ^ μ)) - φ (j.val : ZMod (p ^ μ))) at h
  simpa only [map_natCast, hv] using h

/-- Complete semantic endpoint: all denominator hypotheses are discharged by
the concrete integer-label representation and coefficient embedding. -/
theorem integerCacheRun_correct_auto (μ : ℕ) (hp : p.Prime) (hμ : 0 < μ)
    (φ : ZMod (p ^ μ) →+* R) (v : Fin p → C)
    (hv : ∀ i, ops.decode (v i) = (i.val : R)) (i : Fin p) :
    PolynomialAlgorithm.denote (SubexpDensePolynomial.decodeList ops
      ((integerCacheRun ops μ v).1.getD i.val [])) =
        TableInterpolation.basis (fun i => ops.decode (v i))
          (encodedIntegerUnits ops μ hp φ v hv) i :=
  integerCacheRun_correct ops μ hp hμ φ v hv _ i

theorem integerCacheRun_length (μ : ℕ) (v : Fin p → C) (i : Fin p) :
    ((integerCacheRun ops μ v).1.getD i.val []).length ≤ 1 + 2 * p := by
  exact cacheRun_get_length ops _ _ i

def preprocessingCalls (p μ : ℕ) : ℕ := p ^ 2 * (p + 2 * μ + 9) + p * basisCalls p

include budget

theorem integerCacheRun_cost (μ : ℕ) (v : Fin p → C) :
    (integerCacheRun ops μ v).2 ≤ preprocessingCalls p μ * B := by
  have hi := SubexpResidueInverse.inverseTableRun_cost ops budget v p μ
  have hc := cacheRun_cost ops budget v
    (fun i j => ((SubexpResidueInverse.inverseTableRun ops v p μ).1.get i).get j)
  change _ + _ ≤ _
  simpa only [preprocessingCalls, Nat.add_mul] using Nat.add_le_add hi hc

omit budget

theorem preprocessingCalls_uniform (p μ : ℕ) :
    preprocessingCalls p μ ≤ 32 * (p + μ + 1) ^ 3 := by
  unfold preprocessingCalls basisCalls
  ring_nf
  omega

end SubexponentialSAT.SubexpTableExecution

namespace SubexponentialSAT.SubexpTableExecution

open SubexpTableInterpolation

section Programs

variable {C : Type*} (ops : SubexpSymbolicCost.RingProgram C) {p : ℕ}

def factorProgram (v d : Fin p → C) (i j : Fin p) : List C × ℕ :=
  if i = j then ([ops.oneRun.1], ops.oneRun.2) else
    let product := ops.mulRun (d j) (v j)
    let negative := ops.negRun product.1
    ([negative.1, d j], product.2 + negative.2)

def basisProgram (v d : Fin p → C) (i : Fin p) : List C × ℕ :=
  let factors := mapWithCost (factorProgram ops v d i) (List.finRange p)
  let result := SubexpDensePolynomial.productProgram ops factors.1
  (result.1, factors.2 + result.2)

def cacheProgram (v : Fin p → C) (d : Fin p → Fin p → C) : List (List C) × ℕ :=
  mapWithCost (fun i => basisProgram ops v (d i) i) (List.finRange p)

def integerCacheProgram (μ : ℕ) (v : Fin p → C) : List (List C) × ℕ :=
  let inverses := SubexpResidueInverse.inverseTableProgram ops v p μ
  let cache := cacheProgram ops v (fun i j => (inverses.1.get i).get j)
  (cache.1, inverses.2 + cache.2)

def labelsLoop (one a : C) : ℕ → List C × ℕ
  | 0 => ([], 0)
  | n + 1 =>
      let next := ops.addRun a one
      let rest := labelsLoop one next.1 n
      (a :: rest.1, next.2 + rest.2)

@[simp] theorem labelsLoop_length (one a : C) (n : ℕ) :
    (labelsLoop ops one a n).1.length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [labelsLoop, ih]

/-- Generate all integer labels using a single sequence of additions. -/
def labelsProgram (p : ℕ) : List.Vector C p × ℕ :=
  let zero := ops.zeroRun
  let one := ops.oneRun
  let values := labelsLoop ops one.1 zero.1 p
  (⟨values.1, labelsLoop_length ops one.1 zero.1 p⟩, zero.2 + one.2 + values.2)

/-- Complete runtime table-cache construction, including the label list. -/
def completeProgram (p μ : ℕ) : List (List C) × ℕ :=
  let labels := labelsProgram ops p
  let cache := integerCacheProgram ops μ labels.1.get
  (cache.1, labels.2 + cache.2)

end Programs

section ProgramRefinement

variable {C R : Type*} [CommRing R] (ops : SubexpSymbolicCost.RepresentedRing C R) {p : ℕ}

@[simp] theorem factorProgram_run (v d : Fin p → C) (i j : Fin p) :
    factorProgram ops.program v d i j = factorRun ops v d i j := rfl

@[simp] theorem basisProgram_run (v d : Fin p → C) (i : Fin p) :
    basisProgram ops.program v d i = basisRun ops v d i := by
  simp only [basisProgram, basisRun, SubexpDensePolynomial.productProgram_run]
  rfl

@[simp] theorem cacheProgram_run (v : Fin p → C) (d : Fin p → Fin p → C) :
    cacheProgram ops.program v d = cacheRun ops v d := by
  simp only [cacheProgram, cacheRun, basisProgram_run]

@[simp] theorem integerCacheProgram_run (μ : ℕ) (v : Fin p → C) :
    integerCacheProgram ops.program μ v = integerCacheRun ops μ v := by
  simp only [integerCacheProgram, integerCacheRun,
    SubexpResidueInverse.inverseTableProgram_run, cacheProgram_run]

theorem labelsLoop_decode (one a : C) (hone : ops.decode one = 1) (n : ℕ) :
    ((labelsLoop ops.program one a n).1).map ops.decode =
      List.ofFn (fun i : Fin n => ops.decode a + (i.val : R)) := by
  induction n generalizing a with
  | zero => simp [labelsLoop]
  | succ n ih =>
      simp [labelsLoop, ih, ops.add_correct, hone, List.ofFn_succ,
        Nat.cast_add, add_assoc, add_comm]

theorem labelsProgram_correct (p : ℕ) (i : Fin p) :
    ops.decode ((labelsProgram ops.program p).1.get i) = (i.val : R) := by
  have h := labelsLoop_decode ops ops.oneRun.1 ops.zeroRun.1 ops.one_correct p
  have hi := congrArg (fun xs : List R => xs.getD i.val 0) h
  simp only [ops.zero_correct, zero_add] at hi
  calc
    ops.decode ((labelsProgram ops.program p).1.get i) =
        (List.map ops.decode (labelsLoop ops.program ops.oneRun.1 ops.zeroRun.1 p).1).getD
          i.val 0 := by
      simp only [labelsProgram, List.Vector.get]
      rw [← ops.zero_correct, List.getD_map]
      exact congrArg ops.decode
        (List.getD_eq_get (labelsLoop ops.program ops.oneRun.1 ops.zeroRun.1 p).1
          ops.zeroRun.1
          (i.cast (labelsLoop_length ops.program ops.oneRun.1 ops.zeroRun.1 p).symm)).symm
    _ = (List.ofFn (fun i : Fin p => (i.val : R))).getD i.val 0 := hi
    _ = (i.val : R) := by simp

theorem completeProgram_correct (p μ : ℕ) (hp : p.Prime) (hμ : 0 < μ)
    (φ : ZMod (p ^ μ) →+* R) (i : Fin p) :
    PolynomialAlgorithm.denote (SubexpDensePolynomial.decodeList ops
      ((completeProgram ops.program p μ).1.getD i.val [])) =
      TableInterpolation.basis (fun i => ops.decode ((labelsProgram ops.program p).1.get i))
        (encodedIntegerUnits ops μ hp φ _ (labelsProgram_correct ops p)) i := by
  change PolynomialAlgorithm.denote (SubexpDensePolynomial.decodeList ops
    ((integerCacheProgram ops.program μ (labelsProgram ops.program p).1.get).1.getD i.val [])) = _
  rw [integerCacheProgram_run]
  exact integerCacheRun_correct_auto ops μ hp hμ φ _ (labelsProgram_correct ops p) i

variable {B : ℕ} (budget : SubexpSymbolicCost.ScalarBudget ops B)

include budget

theorem labelsLoop_cost (one a : C) (n : ℕ) :
    (labelsLoop ops.program one a n).2 ≤ n * B := by
  induction n generalizing a with
  | zero => simp [labelsLoop]
  | succ n ih =>
      have ha := budget.add a one
      have hr := ih (ops.addRun a one).1
      change _ + _ ≤ _
      calc
        _ ≤ B + n * B := Nat.add_le_add ha hr
        _ = _ := by ring

theorem labelsProgram_cost (p : ℕ) :
    (labelsProgram ops.program p).2 ≤ (p + 2) * B := by
  have hl := labelsLoop_cost ops budget ops.oneRun.1 ops.zeroRun.1 p
  have hz := budget.zero
  have ho := budget.one
  change _ + _ + _ ≤ _
  calc
    _ ≤ B + B + p * B := Nat.add_le_add (Nat.add_le_add hz ho) hl
    _ = _ := by ring

def completeCalls (p μ : ℕ) : ℕ := p + 2 + preprocessingCalls p μ

theorem completeProgram_cost (p μ : ℕ) :
    (completeProgram ops.program p μ).2 ≤ completeCalls p μ * B := by
  have hl := labelsProgram_cost ops budget p
  have hc := integerCacheRun_cost ops budget μ (labelsProgram ops.program p).1.get
  change _ + _ ≤ _
  rw [integerCacheProgram_run]
  simpa only [completeCalls, Nat.add_mul] using Nat.add_le_add hl hc

end ProgramRefinement

theorem completeCalls_uniform (p μ : ℕ) : completeCalls p μ ≤ 64 * (p + μ + 1) ^ 3 := by
  unfold completeCalls preprocessingCalls basisCalls
  ring_nf
  omega

/-- Concrete prepared-quartic execution. The defining polynomial's semantic
certificate does not occur in the runtime inputs. -/
def preparedTableCache (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (t z o : SubexpSymbolicCost.QuarticCode p D) :=
  completeProgram (SubexpSymbolicCost.preparedProgram p D M t z o) p (D + 1)

theorem preparedTableCache_cost (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (c : Fin 4 → ZMod (p ^ (D + 1))) (t z o : SubexpSymbolicCost.QuarticCode p D)
    (ht : t.map (SubexpQuarticRing.wordValue p (D + 1)) = SubexpQuarticRing.reductionData c)
    (hz : SubexpQuarticRing.quotientDenote c (z.map (SubexpQuarticRing.wordValue p (D + 1))) = 0)
    (ho : SubexpQuarticRing.quotientDenote c (o.map (SubexpQuarticRing.wordValue p (D + 1))) = 1) :
    (preparedTableCache p D M t z o).2 ≤
      completeCalls p (D + 1) * SubexpSymbolicCost.quarticEventBudget D (Nat.log 2 p + 1) := by
  simpa only [SubexpSymbolicCost.preparedRing_program, preparedTableCache] using
    completeProgram_cost (SubexpSymbolicCost.preparedRing p D M c t z o ht hz ho)
      (SubexpSymbolicCost.preparedRing_budget p D M c t z o ht hz ho) p (D + 1)

end SubexponentialSAT.SubexpTableExecution

end OAI.Algorithms
