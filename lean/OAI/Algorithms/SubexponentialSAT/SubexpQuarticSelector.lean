import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.QuarticSearch
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpTupleRefinement
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationPayload

namespace OAI.Algorithms

/-!
# Ordered quartic selection by a concrete record iterator

The control below uses the measured finite-program record iterator. Its
callback contract is discharged by the divisor routines in the subsequent
machine integration. The result identifies the first successful candidate,
so it agrees with the polynomial used by the selected quotient field.
-/

namespace SubexponentialSAT.SubexpQuarticSelector

open BitProgram StructuredCalls
open SubexpTupleRefinement SubexpEnumerationPayload

/-- The stored record is the first successful record, including when earlier
failed callbacks overwrite the same output stack. -/
theorem first_of_visits {r s : ℕ} (output : Fin s)
    (test : List Bool → Bool) {records : List (List Bool)} {base next : State r s}
    (h : RecordPrograms.Visits test (fun bits _ b => b.stacks output = bits)
      records base next)
    (hsuccess : records.any test = true) :
    records.find? test = some (next.stacks output) := by
  induction h with
  | nil base => simp at hsuccess
  | @hit bits rest base next ht he => simp [ht, he]
  | @miss bits rest base middle next ht he history ih =>
      have hr : rest.any test = true := by simpa [ht] using hsuccess
      simpa [ht] using ih hr

theorem find_map_of_test {A B : Type*} (encode : A → B)
    (sourceTest : A → Bool) (targetTest : B → Bool)
    (values : List A) (h : ∀ a ∈ values, targetTest (encode a) = sourceTest a) :
    (values.map encode).find? targetTest = (values.find? sourceTest).map encode := by
  induction values with
  | nil => rfl
  | cons a values ih =>
      have ha := h a (by simp)
      have hr := ih (fun b hb => h b (by simp [hb]))
      cases hs : sourceTest a <;> simp [ha, hs, hr]

theorem first_coefficients (p : ℕ) [Fact p.Prime] :
    (QuarticSearch.vectors (QuarticSearch.elements p) 4).find?
      (QuarticSearch.passes p) = some (QuarticSearch.coefficients p) := by
  have hs : (QuarticSearch.search p).1 =
      (QuarticSearch.vectors (QuarticSearch.elements p) 4).find?
        (QuarticSearch.passes p) := by
    simp only [QuarticSearch.search, QuarticSearch.scan_value, QuarticSearch.evaluate_value]
  rw [← hs]
  cases h : (QuarticSearch.search p).1 with
  | none => exact False.elim (QuarticSearch.search_ne_none p h)
  | some c => simp [QuarticSearch.coefficients, h]

def candidateRecords (p : ℕ) [Fact p.Prime] : List (List Bool) :=
  (QuarticSearch.vectors (QuarticSearch.elements p) 4).map (encodeTuple (scalarCode p))

@[simp] theorem candidateRecords_length (p : ℕ) [Fact p.Prime] :
    (candidateRecords p).length = p^4 := by
  simp [candidateRecords, QuarticSearch.length_vectors]

theorem candidateRecord_width (p : ℕ) [Fact p.Prime]
    (bits : List Bool) (h : bits ∈ candidateRecords p) :
    bits.length = 4 * scalarWidth p := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
  simp [encodeTuple, scalarCode]
  omega

theorem first_candidateRecord (p : ℕ) [Fact p.Prime]
    (test : List Bool → Bool)
    (htest : ∀ c, test (encodeTuple (scalarCode p) c) = QuarticSearch.passes p c) :
    (candidateRecords p).find? test =
      some (encodeTuple (scalarCode p) (QuarticSearch.coefficients p)) := by
  rw [candidateRecords, find_map_of_test _ (QuarticSearch.passes p) test _
    (fun c _ => htest c), first_coefficients]
  rfl

theorem candidateRecords_success (p : ℕ) [Fact p.Prime]
    (test : List Bool → Bool)
    (htest : ∀ c, test (encodeTuple (scalarCode p) c) = QuarticSearch.passes p c) :
    (candidateRecords p).any test = true := by
  obtain ⟨c, hc, hp⟩ := QuarticSearch.exists_passing p
  apply List.any_eq_true.mpr
  exact ⟨encodeTuple (scalarCode p) c, List.mem_map.mpr ⟨c, hc, rfl⟩,
    (htest c).trans hp⟩

theorem uniform_budget (records : List (List Bool)) (width cost : ℕ)
    (hwidth : ∀ bits ∈ records, bits.length = width) :
    RecordPrograms.budget (fun _ => cost) records =
      records.length * (6 * width + cost + 7) := by
  induction records with
  | nil => simp [RecordPrograms.budget]
  | cons bits records ih =>
      have hb := hwidth bits (by simp)
      have hr := ih (fun b h => hwidth b (by simp [h]))
      simp only [RecordPrograms.budget, hb, hr, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- Ordered, measured candidate selection. The only callback premise concerns
execution of its supplied finite code; the controller and output identification
are proved here. -/
theorem select_eval {r s : ℕ} (p : ℕ) [Fact p.Prime]
    (ports : RecordPrograms.Ports r s) (callback : Cmd r s) (output : Fin s)
    (test : List Bool → Bool) (callbackCost : ℕ)
    (invariant : State r s → Prop)
    (htest : ∀ c, test (encodeTuple (scalarCode p) c) = QuarticSearch.passes p c)
    (contract : RecordPrograms.CallbackContractWithOn ports callback test
      (fun _ => callbackCost) invariant (fun bits _ b => b.stacks output = bits)
      (fun bits => bits ∈ candidateRecords p))
    (base : State r s) (hbase : invariant base)
    (suffix : List Bool) (v pr result : Bool) :
    ∃ n next,
      n ≤ 3 + p^4 * (24 * scalarWidth p + callbackCost + 7) ∧ invariant next ∧
      next.stacks output = encodeTuple (scalarCode p) (QuarticSearch.coefficients p) ∧
      Eval (RecordPrograms.iterate ports callback) n
        (RecordPrograms.state ports base v pr result
          (ProgramEncoding.encodeRecords (candidateRecords p) ++ suffix) [])
        (RecordPrograms.state ports next false true true
          (RecordPrograms.unread test (candidateRecords p) suffix) []) := by
  have hs := candidateRecords_success p test htest
  obtain ⟨n, next, hn, hi, history, run⟩ := RecordPrograms.iterate_run_with_on
    ports callback test (fun _ => callbackCost) invariant
    (fun bits _ b => b.stacks output = bits) (fun bits => bits ∈ candidateRecords p)
    contract (candidateRecords p) suffix base (fun _ h => h) hbase v pr result
  have hout := first_of_visits output test history hs
  rw [first_candidateRecord p test htest] at hout
  have hb := uniform_budget (candidateRecords p) (4 * scalarWidth p) callbackCost
    (candidateRecord_width p)
  rw [candidateRecords_length] at hb
  refine ⟨n, next, ?_, hi, (Option.some.inj hout).symm, ?_⟩
  · rw [hb] at hn
    simpa only [show 6 * (4 * scalarWidth p) = 24 * scalarWidth p by omega] using hn
  · simpa only [hs] using run

end SubexponentialSAT.SubexpQuarticSelector

end OAI.Algorithms
