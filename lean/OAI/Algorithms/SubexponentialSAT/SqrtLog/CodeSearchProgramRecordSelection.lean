import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RecordMappedPrograms

namespace OAI.Algorithms

/-! A refinement of the existing fixed record iterator: the returned base
state retains the last success flag. This supports a flag-to-cached-witness
invariant without assuming that record-state overwrites preserve success. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram.RecordSelection
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms
variable {α : Type*} {r s : ℕ}

abbrev Contract (p : Ports r s) (callback : Cmd r s) (enc : α → List Bool)
    (test : α → Bool) (cost : α → ℕ) (invariant : State r s → Prop) : Prop :=
  ∀ (a : α) (tail : List Bool) (base : State r s), invariant base →
    ∃ (n : ℕ) (next : State r s), n ≤ cost a ∧ invariant next ∧
      next.regs p.found = test a ∧
      Eval callback n (state p base false true false tail (enc a).reverse)
        (state p next false true (test a) tail [])

theorem loop_run (p : Ports r s) (callback : Cmd r s) (enc : α → List Bool)
    (test : α → Bool) (cost : α → ℕ) (invariant : State r s → Prop)
    (contract : Contract p callback enc test cost invariant)
    (reset : ∀ base, invariant base → ∀ suffix,
      invariant (state p base false true false suffix []))
    (values : List α) (suffix : List Bool) (base : State r s)
    (valid : invariant base) :
    ∃ (n : ℕ) (next : State r s), n ≤ 1 + RecordMappedPrograms.budget enc cost values ∧ invariant next ∧
      next.regs p.found = values.any test ∧
      Eval (RecordPrograms.loop p callback) n (RecordMappedPrograms.afterTag p enc base values suffix)
        (state p next false true (values.any test) (RecordMappedPrograms.unread enc test values suffix) []) := by
  induction values generalizing base with
  | nil =>
      refine ⟨1,state p base false true false suffix [],by simp [RecordMappedPrograms.budget],
        reset base valid suffix,by simp,?_⟩
      simpa [RecordMappedPrograms.afterTag,RecordMappedPrograms.unread] using
        (Eval.while_false (test := p.tag) (body := RecordPrograms.body p callback)
          (a := state p base false true false suffix []) (by simp))
  | cons a rest ih =>
      let tail := Encoding.encodeList enc rest ++ suffix
      obtain ⟨n,middle,hn,hmiddle,hflag,hcallback⟩ := contract a tail base valid
      have hreader : Eval (reader p) (6 * (enc a).length + 4)
          (RecordMappedPrograms.afterTag p enc base (a :: rest) suffix)
          (state p base false true false tail (enc a).reverse) := by
        simpa [RecordMappedPrograms.afterTag,tail] using reader_eval p base (enc a) tail [] true true false
      have hguard : (RecordMappedPrograms.afterTag p enc base (a :: rest) suffix).regs p.tag = true := by
        simp [RecordMappedPrograms.afterTag]
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
          refine ⟨(6 * (enc a).length + 4 + (n + 2)) + 1 + 1,
            middle,?_,hmiddle,?_,?_⟩
          · simp only [RecordMappedPrograms.budget]; omega
          · simpa [ht] using hflag
          · simpa [RecordPrograms.loop,body,RecordMappedPrograms.unread,ht,tail] using hrun
      | false =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test a) tail [])
              (RecordMappedPrograms.afterTag p enc middle rest suffix) := by
            rw [ht]
            apply Eval.ite_false (by simp)
            exact RecordMappedPrograms.pop_list_eval p enc middle rest suffix false true
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          obtain ⟨m,next,hm,hnext,hnextflag,hrest⟩ := ih middle hmiddle
          have hrun := Eval.while_true hguard hbody hrest
          refine ⟨(6 * (enc a).length + 4 + (n + 2)) + m + 1,next,?_,hnext,?_,?_⟩
          · simp only [RecordMappedPrograms.budget]; omega
          · simpa [ht] using hnextflag
          · simpa [RecordPrograms.loop,body,RecordMappedPrograms.unread,ht] using hrun

theorem iterate_run (p : Ports r s) (callback : Cmd r s) (enc : α → List Bool)
    (test : α → Bool) (cost : α → ℕ) (invariant : State r s → Prop)
    (contract : Contract p callback enc test cost invariant)
    (reset : ∀ base, invariant base → ∀ suffix,
      invariant (state p base false true false suffix []))
    (values : List α) (suffix : List Bool) (base : State r s)
    (valid : invariant base) (v pr f : Bool) :
    ∃ (n : ℕ) (next : State r s), n ≤ 3 + RecordMappedPrograms.budget enc cost values ∧ invariant next ∧
      next.regs p.found = values.any test ∧
      Eval (RecordPrograms.iterate p callback) n
        (state p base v pr f (Encoding.encodeList enc values ++ suffix) [])
        (state p next false true (values.any test) (RecordMappedPrograms.unread enc test values suffix) []) := by
  obtain ⟨n,next,hn,hnext,hflag,hloop⟩ :=
    loop_run p callback enc test cost invariant contract reset values suffix base valid
  refine ⟨1+(1+n),next,by omega,hnext,hflag,?_⟩
  exact Eval.seq (set_found_eval p base v pr f false _ [])
    (Eval.seq (RecordMappedPrograms.pop_list_eval p enc base values suffix v pr) hloop)

end SubexponentialSAT.SqrtLog.CodeSearchProgram.RecordSelection

end OAI.Algorithms
