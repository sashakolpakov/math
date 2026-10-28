import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramRecords

namespace OAI.Algorithms

/-! A measured physical record fold with accumulator-dependent cost. This
retains the actual fixed callback and parser; the cost recurrence can account
for changing sparse dictionary lengths without postulating a uniform bound. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.DynamicFold
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms

variable {r s : ℕ} {R A : Type*}

abbrev value (step : R → A → A) : List R → A → A
  | [], a => a
  | x::xs, a => value step xs (step x a)

abbrev work (encode : R → List Bool) (step : R → A → A) (cost : R → A → ℕ) : List R → A → ℕ
  | [], _ => 0
  | x::xs, a => 6*(encode x).length+cost x a+7+work encode step cost xs (step x a)

/-- A refinement relation may track the sparse accumulator and arbitrary
persistent machine context. The callback must consume its parsed payload. -/
abbrev Contract (p : Ports r s) (callback : Cmd r s) (encode : R → List Bool)
    (step : R → A → A) (cost : R → A → ℕ) (Rep : A → State r s → Prop) : Prop :=
  ∀ x a base, Rep a base → ∀ tail,
    ∃ n next, n ≤ cost x a ∧ Rep (step x a) next ∧
      Eval callback n (state p base false true false tail (encode x).reverse)
        (state p next false true false tail [])

theorem loop_eval (p : Ports r s) (callback : Cmd r s) (encode : R → List Bool)
    (step : R → A → A) (cost : R → A → ℕ) (Rep : A → State r s → Prop)
    (hc : Contract p callback encode step cost Rep)
    (xs : List R) (a : A) (base : State r s) (hb : Rep a base) (suffix : List Bool) :
    ∃ n next, n ≤ 1+work encode step cost xs a ∧ Rep (value step xs a) next ∧
      Eval (loop p callback) n (afterTag p base (xs.map encode) suffix)
        (state p next false true false suffix []) := by
  induction xs generalizing a base with
  | nil =>
    refine ⟨1,base,by simp [work],hb,?_⟩
    apply Eval.while_false
    simp [afterTag]
  | cons x xs ih =>
    let tail := Encoding.encodeList id (xs.map encode) ++ suffix
    obtain ⟨n,middle,hn,hm,hcallback⟩ := hc x a base hb tail
    have hreader : Eval (reader p) (6*(encode x).length+4)
        (afterTag p base ((x::xs).map encode) suffix)
        (state p base false true false tail (encode x).reverse) := by
      simpa [afterTag,tail] using reader_eval p base (encode x) tail [] true true false
    have hguard : (afterTag p base ((x::xs).map encode) suffix).regs p.tag = true := by
      simp [afterTag]
    have hbranch : Eval (.ite p.found (atom (.set p.tag false))
        (atom (.pop p.source p.tag p.present))) 2
        (state p middle false true false tail [])
        (afterTag p middle (xs.map encode) suffix) := by
      apply Eval.ite_false (by simp)
      exact pop_list_eval p middle (xs.map encode) suffix false true
    obtain ⟨m,next,hmb,hr,hrest⟩ := ih (step x a) middle hm
    have run := Eval.while_true hguard (hreader.seq (hcallback.seq hbranch)) hrest
    refine ⟨(6*(encode x).length+4+(n+2))+m+1,next,?_,hr,?_⟩
    · simp only [work]; omega
    · simpa [loop,body] using run

theorem command_eval (p : Ports r s) (callback : Cmd r s) (encode : R → List Bool)
    (step : R → A → A) (cost : R → A → ℕ) (Rep : A → State r s → Prop)
    (hc : Contract p callback encode step cost Rep)
    (xs : List R) (a : A) (base : State r s) (hb : Rep a base) (suffix : List Bool)
    (v pr f : Bool) :
    ∃ n next, n ≤ 3+work encode step cost xs a ∧ Rep (value step xs a) next ∧
      Eval (iterate p callback) n
        (state p base v pr f (Encoding.encodeList id (xs.map encode) ++ suffix) [])
        (state p next false true false suffix []) := by
  obtain ⟨n,next,hn,hr,hloop⟩ := loop_eval p callback encode step cost Rep hc xs a base hb suffix
  exact ⟨1+(1+n),next,by omega,hr,
    (set_found_eval p base v pr f false _ []).seq
      ((pop_list_eval p base (xs.map encode) suffix v pr).seq hloop)⟩

theorem value_eq_foldl (step : R → A → A) (xs : List R) (a : A) :
    value step xs a = xs.foldl (fun a x => step x a) a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => exact ih (step x a)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.DynamicFold

end OAI.Algorithms
