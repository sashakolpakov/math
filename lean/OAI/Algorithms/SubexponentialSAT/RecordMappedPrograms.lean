import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RecordPrograms

namespace OAI.Algorithms

/-!
# Actual record iteration over encoded logical values

The instruction sequence is `RecordPrograms.iterate`. The contract below is
required only for payloads emitted by the supplied encoder. It does not ask a
callback for correct behavior on malformed encodings, and it does not install
the encoder, test, or cost function as a machine instruction.
-/

namespace SubexponentialSAT.RecordMappedPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms

variable {α : Type*} {r s : ℕ}

abbrev Contract (p : Ports r s) (callback : Cmd r s) (enc : α → List Bool)
    (test : α → Bool) (cost : α → ℕ) (invariant : State r s → Prop) : Prop :=
  ∀ (a : α) (tail : List Bool) (base : State r s), invariant base →
    ∃ (n : ℕ) (next : State r s), n ≤ cost a ∧ invariant next ∧
      Eval callback n (state p base false true false tail (enc a).reverse)
        (state p next false true (test a) tail [])

def unread (enc : α → List Bool) (test : α → Bool) : List α → List Bool → List Bool
  | [], suffix => suffix
  | a :: rest, suffix =>
      if test a then Encoding.encodeList enc rest ++ suffix else unread enc test rest suffix

def budget (enc : α → List Bool) (cost : α → ℕ) : List α → ℕ
  | [] => 0
  | a :: rest => 6 * (enc a).length + cost a + 7 + budget enc cost rest

def afterTag (p : Ports r s) (enc : α → List Bool) (base : State r s)
    (values : List α) (suffix : List Bool) : State r s :=
  match values with
  | [] => state p base false true false suffix []
  | a :: rest => state p base true true false
      (Encoding.frame (enc a) ++ (Encoding.encodeList enc rest ++ suffix)) []

theorem pop_list_eval (p : Ports r s) (enc : α → List Bool) (base : State r s)
    (values : List α) (suffix : List Bool) (v pr : Bool) :
    Eval (atom (.pop p.source p.tag p.present)) 1
      (state p base v pr false (Encoding.encodeList enc values ++ suffix) [])
      (afterTag p enc base values suffix) := by
  cases values with
  | nil =>
      simpa [Encoding.encodeList, afterTag] using
        RecordPrograms.pop_eval p base v pr false false suffix []
  | cons a rest =>
      simpa [Encoding.encodeList, afterTag, List.append_assoc] using
        RecordPrograms.pop_eval p base v pr false true
          (Encoding.frame (enc a) ++ (Encoding.encodeList enc rest ++ suffix)) []

theorem loop_run (p : Ports r s) (callback : Cmd r s) (enc : α → List Bool)
    (test : α → Bool) (cost : α → ℕ) (invariant : State r s → Prop)
    (contract : Contract p callback enc test cost invariant)
    (values : List α) (suffix : List Bool) (base : State r s)
    (valid : invariant base) :
    ∃ (n : ℕ) (next : State r s), n ≤ 1 + budget enc cost values ∧ invariant next ∧
      Eval (RecordPrograms.loop p callback) n (afterTag p enc base values suffix)
        (state p next false true (values.any test) (unread enc test values suffix) []) := by
  induction values generalizing base with
  | nil =>
      refine ⟨1, base, by simp [budget], valid, ?_⟩
      apply Eval.while_false
      simp [afterTag]
  | cons a rest ih =>
      let tail := Encoding.encodeList enc rest ++ suffix
      obtain ⟨n, middle, hn, hmiddle, hcallback⟩ := contract a tail base valid
      have hreader : Eval (reader p) (6 * (enc a).length + 4)
          (afterTag p enc base (a :: rest) suffix)
          (state p base false true false tail (enc a).reverse) := by
        simpa [afterTag, tail] using reader_eval p base (enc a) tail [] true true false
      have hguard : (afterTag p enc base (a :: rest) suffix).regs p.tag = true := by
        simp [afterTag]
      cases ht : test a with
      | true =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test a) tail [])
              (state p middle false true true tail []) := by
            rw [ht]
            apply Eval.ite_true (by simp)
            exact set_tag_eval p middle false true true false tail []
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          have hfinish : Eval (RecordPrograms.loop p callback) 1
              (state p middle false true true tail [])
              (state p middle false true true tail []) := Eval.while_false (by simp)
          have hrun := Eval.while_true hguard hbody hfinish
          refine ⟨(6 * (enc a).length + 4 + (n + 2)) + 1 + 1, middle, ?_, hmiddle, ?_⟩
          · simp only [budget]
            omega
          · simpa [RecordPrograms.loop, body, unread, ht, tail] using hrun
      | false =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test a) tail [])
              (afterTag p enc middle rest suffix) := by
            rw [ht]
            apply Eval.ite_false (by simp)
            exact pop_list_eval p enc middle rest suffix false true
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          obtain ⟨m, next, hm, hnext, hrest⟩ := ih middle hmiddle
          have hrun := Eval.while_true hguard hbody hrest
          refine ⟨(6 * (enc a).length + 4 + (n + 2)) + m + 1, next, ?_, hnext, ?_⟩
          · simp only [budget]
            omega
          · simpa [RecordPrograms.loop, body, unread, ht] using hrun

/-- Genuine execution of one fixed iterator over any list of encodable values.
The encoder appears only in the input/output specification and bound. -/
theorem iterate_run (p : Ports r s) (callback : Cmd r s) (enc : α → List Bool)
    (test : α → Bool) (cost : α → ℕ) (invariant : State r s → Prop)
    (contract : Contract p callback enc test cost invariant)
    (values : List α) (suffix : List Bool) (base : State r s)
    (valid : invariant base) (v pr f : Bool) :
    ∃ (n : ℕ) (next : State r s), n ≤ 3 + budget enc cost values ∧ invariant next ∧
      Eval (RecordPrograms.iterate p callback) n
        (state p base v pr f (Encoding.encodeList enc values ++ suffix) [])
        (state p next false true (values.any test) (unread enc test values suffix) []) := by
  obtain ⟨n, next, hn, hnext, hloop⟩ := loop_run p callback enc test cost invariant contract
    values suffix base valid
  refine ⟨1 + (1 + n), next, by omega, hnext, ?_⟩
  exact Eval.seq (set_found_eval p base v pr f false _ [])
    (Eval.seq (pop_list_eval p enc base values suffix v pr) hloop)

theorem unread_length_le (enc : α → List Bool) (test : α → Bool)
    (values : List α) (suffix : List Bool) :
    (unread enc test values suffix).length ≤
      (Encoding.encodeList enc values).length + suffix.length := by
  induction values with
  | nil => simp [unread, Encoding.encodeList]
  | cons a rest ih =>
      cases h : test a <;>
        simp [unread, h, Encoding.length_encodeList_cons] ; omega

/-- A linear bound in the actual encoded input length, provided the callback
bound is linear in its current encoded payload length. -/
theorem program_budget_le_input (enc : α → List Bool) (cost : α → ℕ)
    (values : List α) (a b : ℕ)
    (hcost : ∀ x ∈ values, cost x ≤ a * (enc x).length + b) :
    4 + budget enc cost values ≤
      (a + b + 17) * ((Encoding.encodeList enc values).length + 1) := by
  induction values with
  | nil => simp [budget, Encoding.encodeList]; omega
  | cons x xs ih =>
      have hx := hcost x (by simp)
      have ht := ih (fun y hy => hcost y (by simp [hy]))
      simp only [budget, Encoding.length_encodeList_cons]
      nlinarith

end SubexponentialSAT.RecordMappedPrograms

end OAI.Algorithms
