import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.ParserProgram
import OAI.Algorithms.SubexponentialSAT.ProgramEncoding

namespace OAI.Algorithms

/-! A reusable actual iterator over the project's framed-record representation.
The callback is a fixed structured program, whose executions are measured in the
same semantics as the parser and iterator. It is never an atomic semantic oracle.
-/

namespace SubexponentialSAT.RecordPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

structure Ports (r s : ℕ) where
  tag : Fin r
  present : Fin r
  found : Fin r
  source : Fin s
  payload : Fin s
  tag_ne_present : tag ≠ present
  found_ne_tag : found ≠ tag
  found_ne_present : found ≠ present
  source_ne_payload : source ≠ payload

def state {r s : ℕ} (p : Ports r s) (base : State r s)
    (tagValue presentValue foundValue : Bool) (sourceWord payloadWord : List Bool) :
    State r s :=
  ⟨Function.update (Function.update (Function.update base.regs p.tag tagValue)
      p.present presentValue) p.found foundValue,
    Function.update (Function.update base.stacks p.source sourceWord) p.payload payloadWord⟩

@[simp] theorem state_tag {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f : Bool) (src out : List Bool) : (state p base v pr f src out).regs p.tag = v := by
  simp [state, p.tag_ne_present, Ne.symm p.found_ne_tag]

@[simp] theorem state_present {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f : Bool) (src out : List Bool) : (state p base v pr f src out).regs p.present = pr := by
  simp [state, Ne.symm p.found_ne_present]

@[simp] theorem state_found {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f : Bool) (src out : List Bool) : (state p base v pr f src out).regs p.found = f := by
  simp [state]

@[simp] theorem state_source {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f : Bool) (src out : List Bool) : (state p base v pr f src out).stacks p.source = src := by
  simp [state, p.source_ne_payload]

@[simp] theorem state_payload {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f : Bool) (src out : List Bool) : (state p base v pr f src out).stacks p.payload = out := by
  simp [state]

theorem state_register_frame {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f : Bool) (src out : List Bool) (i : Fin r)
    (ht : i ≠ p.tag) (hp : i ≠ p.present) (hf : i ≠ p.found) :
    (state p base v pr f src out).regs i = base.regs i := by
  simp [state, ht, hp, hf]

theorem state_stack_frame {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f : Bool) (src out : List Bool) (i : Fin s)
    (hs : i ≠ p.source) (hp : i ≠ p.payload) :
    (state p base v pr f src out).stacks i = base.stacks i := by
  simp [state, hs, hp]

theorem state_eq_self {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f : Bool) (src out : List Bool)
    (ht : base.regs p.tag = v) (hp : base.regs p.present = pr)
    (hf : base.regs p.found = f) (hs : base.stacks p.source = src)
    (ho : base.stacks p.payload = out) : state p base v pr f src out = base := by
  cases base with
  | mk regs stk =>
      simp only at ht hp hf hs ho
      simp only [state]
      congr 1
      · funext i
        by_cases hit : i = p.tag <;> by_cases hip : i = p.present <;>
          by_cases hif : i = p.found <;> subst_vars <;>
          simp_all []
      · funext i
        by_cases his : i = p.source <;> by_cases hio : i = p.payload <;>
          subst_vars <;> simp_all []

@[simp] theorem state_state {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f v' pr' f' : Bool) (src out src' out' : List Bool) :
    state p (state p base v pr f src out) v' pr' f' src' out' =
      state p base v' pr' f' src' out' := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases hit : i = p.tag <;> by_cases hip : i = p.present <;>
      by_cases hif : i = p.found <;> simp [state, Function.update_apply, hit, hip, hif]
  · funext i
    by_cases his : i = p.source <;> by_cases hio : i = p.payload <;>
      simp [state, Function.update_apply, his, hio]

def registerMap {r s : ℕ} (p : Ports r s) (i : Fin 2) : Fin r :=
  if i = 0 then p.tag else p.present

def stackMap {r s : ℕ} (p : Ports r s) (i : Fin 2) : Fin s :=
  if i = 0 then p.source else p.payload

theorem registerMap_injective {r s : ℕ} (p : Ports r s) : Function.Injective (registerMap p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [registerMap, p.tag_ne_present, Ne.symm p.tag_ne_present]

theorem stackMap_injective {r s : ℕ} (p : Ports r s) : Function.Injective (stackMap p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [stackMap, p.source_ne_payload, Ne.symm p.source_ne_payload]

abbrev reader {r s : ℕ} (p : Ports r s) : Cmd r s :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram (registerMap p) (stackMap p))

abbrev atom {r s : ℕ} (a : StructuredProgram.Atom r s) : Cmd r s := .base (.atom a)

abbrev body {r s : ℕ} (p : Ports r s) (callback : Cmd r s) : Cmd r s :=
  .seq (reader p) (.seq callback
    (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))))

abbrev loop {r s : ℕ} (p : Ports r s) (callback : Cmd r s) : Cmd r s :=
  .while p.tag (body p callback)

abbrev iterate {r s : ℕ} (p : Ports r s) (callback : Cmd r s) : Cmd r s :=
  .seq (atom (.set p.found false))
    (.seq (atom (.pop p.source p.tag p.present)) (loop p callback))

/-- The contract describes measured executions of the fixed callback code.
Only the actual parser and callback execute; the predicate and budget are specs. -/
abbrev CallbackContract {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop) : Prop :=
  ∀ (bits tail : List Bool) (base : State r s), invariant base →
    ∃ (n : ℕ) (next : State r s), n ≤ cost bits ∧ invariant next ∧
      Eval callback n (state p base false true false tail bits.reverse)
        (state p next false true (test bits) tail [])

def unread (test : List Bool → Bool) : List (List Bool) → List Bool → List Bool
  | [], suffix => suffix
  | bits :: rest, suffix =>
      if test bits then Encoding.encodeList id rest ++ suffix else unread test rest suffix

def budget (cost : List Bool → ℕ) : List (List Bool) → ℕ
  | [] => 0
  | bits :: rest => 6 * bits.length + cost bits + 7 + budget cost rest

private theorem extend_pair {α β : Type} [DecidableEq α] (x y : α) (hxy : x ≠ y)
    (a b : β) (base : α → β) :
    Function.extend (ParserProgram.pair x y) (ParserProgram.pair a b) base =
      Function.update (Function.update base x a) y b := by
  classical
  have hinj : Function.Injective (ParserProgram.pair x y) := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [ParserProgram.pair, Ne.symm hxy]
  funext z
  by_cases hx : z = x
  · subst z
    have h := hinj.extend_apply (ParserProgram.pair a b) base (0 : Fin 2)
    simpa [ParserProgram.pair, hxy] using h
  · by_cases hy : z = y
    · subst z
      have h := hinj.extend_apply (ParserProgram.pair a b) base (1 : Fin 2)
      simpa [ParserProgram.pair] using h
    · have hout : ¬ ∃ i, ParserProgram.pair x y i = z := by
        rintro ⟨i, hi⟩
        fin_cases i <;> simp [ParserProgram.pair] at hi <;> subst z <;> contradiction
      rw [Function.extend_apply' _ _ _ hout]
      simp [hx, hy]

def parserState (v pr : Bool) (src out : List Bool) : State 2 2 :=
  ⟨ParserProgram.pair v pr, ParserProgram.pair src out⟩

theorem embed_parserState {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f v' pr' : Bool) (src out src' out' : List Bool) :
    embedState (registerMap p) (stackMap p) (state p base v pr f src out)
      (parserState v' pr' src' out') = state p base v' pr' f src' out' := by
  unfold embedState parserState
  change StructuredProgram.State.mk
    (Function.extend (ParserProgram.pair p.tag p.present) (ParserProgram.pair v' pr') _)
    (Function.extend (ParserProgram.pair p.source p.payload) (ParserProgram.pair src' out') _) = _
  rw [extend_pair _ _ p.tag_ne_present, extend_pair _ _ p.source_ne_payload]
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases ht : i = p.tag <;> by_cases hp : i = p.present <;> by_cases hf : i = p.found <;>
      simp_all [state, Function.update_apply, p.found_ne_tag, p.found_ne_present,
        p.tag_ne_present]
  · funext i
    by_cases hs : i = p.source <;> by_cases hp : i = p.payload <;>
      simp_all [state, Function.update_apply]

/-- The callback receives the reversed payload, with every auxiliary port framed. -/
theorem reader_eval {r s : ℕ} (p : Ports r s) (base : State r s)
    (bits tail out : List Bool) (v pr f : Bool) :
    Eval (reader p) (6 * bits.length + 4)
      (state p base v pr f (Encoding.frame bits ++ tail) out)
      (state p base false true f tail (bits.reverse ++ out)) := by
  have h := eval_call_lifted ParserProgram.frameProgram (registerMap p) (stackMap p)
    (state p base v pr f (Encoding.frame bits ++ tail) out)
    (registerMap_injective p) (stackMap_injective p)
    (a := parserState v pr (Encoding.frame bits ++ tail) out)
    (b := parserState false true tail (bits.reverse ++ out))
    (ParserProgram.frame_trace bits tail out v pr)
  simpa only [embed_parserState, reader] using h

theorem set_found_eval {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f f' : Bool) (src out : List Bool) :
    Eval (atom (.set p.found f')) 1 (state p base v pr f src out)
      (state p base v pr f' src out) := by
  have h : (StructuredProgram.Atom.set p.found f').eval (state p base v pr f src out) =
      state p base v pr f' src out := by
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, state]
  rw [← h]
  exact .base (.atom _ _)

theorem set_tag_eval {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f v' : Bool) (src out : List Bool) :
    Eval (atom (.set p.tag v')) 1 (state p base v pr f src out)
      (state p base v' pr f src out) := by
  have h : (StructuredProgram.Atom.set p.tag v').eval (state p base v pr f src out) =
      state p base v' pr f src out := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      by_cases ht : i = p.tag <;> by_cases hp : i = p.present <;> by_cases hf : i = p.found <;>
        simp_all [ StructuredProgram.Atom.instr, execInstr,
          state, p.found_ne_tag, p.tag_ne_present,
          Ne.symm p.tag_ne_present]
    · rfl
  rw [← h]
  exact .base (.atom _ _)

theorem pop_eval {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f b : Bool) (src out : List Bool) :
    Eval (atom (.pop p.source p.tag p.present)) 1 (state p base v pr f (b :: src) out)
      (state p base b true f src out) := by
  have h : (StructuredProgram.Atom.pop p.source p.tag p.present).eval
      (state p base v pr f (b :: src) out) = state p base b true f src out := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      by_cases ht : i = p.tag <;> by_cases hp : i = p.present <;> by_cases hf : i = p.found <;>
        simp_all [ StructuredProgram.Atom.instr, execInstr,
          readRegs, state, p.found_ne_tag, p.found_ne_present,
          p.tag_ne_present, p.source_ne_payload]
    · funext i
      by_cases hs : i = p.source <;> by_cases hp : i = p.payload <;>
        simp_all [ StructuredProgram.Atom.instr, execInstr,
          state, p.source_ne_payload, Ne.symm p.source_ne_payload]
  rw [← h]
  exact .base (.atom _ _)

/-- State just after the outer list marker has been read. -/
def afterTag {r s : ℕ} (p : Ports r s) (base : State r s)
    (records : List (List Bool)) (suffix : List Bool) : State r s :=
  match records with
  | [] => state p base false true false suffix []
  | bits :: rest => state p base true true false
      (Encoding.frame bits ++ (Encoding.encodeList id rest ++ suffix)) []

theorem pop_list_eval {r s : ℕ} (p : Ports r s) (base : State r s)
    (records : List (List Bool)) (suffix : List Bool) (v pr : Bool) :
    Eval (atom (.pop p.source p.tag p.present)) 1
      (state p base v pr false (Encoding.encodeList id records ++ suffix) [])
      (afterTag p base records suffix) := by
  cases records with
  | nil => simpa [Encoding.encodeList, afterTag] using pop_eval p base v pr false false suffix []
  | cons bits rest =>
      simpa [Encoding.encodeList, afterTag, List.append_assoc] using
        pop_eval p base v pr false true
          (Encoding.frame bits ++ (Encoding.encodeList id rest ++ suffix)) []

/-- Measured loop execution, including the final failed loop guard. -/
theorem loop_run {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (contract : CallbackContract p callback test cost invariant)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (valid : invariant base) :
    ∃ (n : ℕ) (next : State r s), n ≤ 1 + budget cost records ∧ invariant next ∧
      Eval (loop p callback) n (afterTag p base records suffix)
        (state p next false true (records.any test) (unread test records suffix) []) := by
  induction records generalizing base with
  | nil =>
      refine ⟨1, base, by simp [budget], valid, ?_⟩
      apply Eval.while_false
      simp [afterTag]
  | cons bits rest ih =>
      let tail := Encoding.encodeList id rest ++ suffix
      obtain ⟨n, middle, hn, hmiddle, hcallback⟩ := contract bits tail base valid
      have hreader : Eval (reader p) (6 * bits.length + 4)
          (afterTag p base (bits :: rest) suffix)
          (state p base false true false tail bits.reverse) := by
        simpa [afterTag, tail] using reader_eval p base bits tail [] true true false
      have hguard : (afterTag p base (bits :: rest) suffix).regs p.tag = true := by
        simp [afterTag]
      cases ht : test bits with
      | true =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test bits) tail [])
              (state p middle false true true tail []) := by
            rw [ht]
            apply Eval.ite_true (by simp)
            exact set_tag_eval p middle false true true false tail []
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          have hfinish : Eval (loop p callback) 1
              (state p middle false true true tail [])
              (state p middle false true true tail []) :=
            Eval.while_false (by simp)
          have hrun := Eval.while_true hguard hbody hfinish
          refine ⟨(6 * bits.length + 4 + (n + 2)) + 1 + 1, middle, ?_, hmiddle, ?_⟩
          · simp only [budget]
            omega
          · simpa [loop, body, unread, ht, tail] using hrun
      | false =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test bits) tail [])
              (afterTag p middle rest suffix) := by
            rw [ht]
            apply Eval.ite_false (by simp)
            exact pop_list_eval p middle rest suffix false true
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          obtain ⟨m, next, hm, hnext, hrest⟩ := ih middle hmiddle
          have hrun := Eval.while_true hguard hbody hrest
          refine ⟨(6 * bits.length + 4 + (n + 2)) + m + 1, next, ?_, hnext, ?_⟩
          · simp only [budget]
            omega
          · simpa [loop, body, unread, ht] using hrun

/-- One fixed iterator handles all record counts and payload lengths. The
bound sums genuine callback executions and parser/guard instructions. -/
theorem iterate_run {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (contract : CallbackContract p callback test cost invariant)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (valid : invariant base) (v pr f : Bool) :
    ∃ (n : ℕ) (next : State r s), n ≤ 3 + budget cost records ∧ invariant next ∧
      Eval (iterate p callback) n
        (state p base v pr f (Encoding.encodeList id records ++ suffix) [])
        (state p next false true (records.any test) (unread test records suffix) []) := by
  obtain ⟨n, next, hn, hnext, hloop⟩ := loop_run p callback test cost invariant contract
    records suffix base valid
  refine ⟨1 + (1 + n), next, by omega, hnext, ?_⟩
  exact Eval.seq (set_found_eval p base v pr f false _ [])
    (Eval.seq (pop_list_eval p base records suffix v pr) hloop)

/-- A callback contract that additionally records its change to auxiliary data. -/
abbrev CallbackContractWith {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (effect : List Bool → State r s → State r s → Prop) : Prop :=
  ∀ (bits tail : List Bool) (base : State r s), invariant base →
    ∃ (n : ℕ) (next : State r s), n ≤ cost bits ∧ invariant next ∧ effect bits base next ∧
      Eval callback n (state p base false true false tail bits.reverse)
        (state p next false true (test bits) tail [])

/-- The ordered auxiliary effects of all callbacks actually visited before
the first successful match, or until the list ends. -/
inductive Visits {r s : ℕ} (test : List Bool → Bool)
    (effect : List Bool → State r s → State r s → Prop) :
    List (List Bool) → State r s → State r s → Prop
  | nil (base) : Visits test effect [] base base
  | hit {bits rest base next} : test bits = true → effect bits base next →
      Visits test effect (bits :: rest) base next
  | miss {bits rest base middle next} : test bits = false → effect bits base middle →
      Visits test effect rest middle next → Visits test effect (bits :: rest) base next

theorem loop_run_with {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (effect : List Bool → State r s → State r s → Prop)
    (contract : CallbackContractWith p callback test cost invariant effect)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (valid : invariant base) :
    ∃ (n : ℕ) (next : State r s), n ≤ 1 + budget cost records ∧ invariant next ∧
      Visits test effect records base next ∧
      Eval (loop p callback) n (afterTag p base records suffix)
        (state p next false true (records.any test) (unread test records suffix) []) := by
  induction records generalizing base with
  | nil =>
      refine ⟨1, base, by simp [budget], valid, Visits.nil _, ?_⟩
      apply Eval.while_false
      simp [afterTag]
  | cons bits rest ih =>
      let tail := Encoding.encodeList id rest ++ suffix
      obtain ⟨n, middle, hn, hmiddle, heffect, hcallback⟩ := contract bits tail base valid
      have hreader : Eval (reader p) (6 * bits.length + 4)
          (afterTag p base (bits :: rest) suffix)
          (state p base false true false tail bits.reverse) := by
        simpa [afterTag, tail] using reader_eval p base bits tail [] true true false
      have hguard : (afterTag p base (bits :: rest) suffix).regs p.tag = true := by
        simp [afterTag]
      cases ht : test bits with
      | true =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test bits) tail [])
              (state p middle false true true tail []) := by
            rw [ht]
            apply Eval.ite_true (by simp)
            exact set_tag_eval p middle false true true false tail []
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          have hfinish : Eval (loop p callback) 1
              (state p middle false true true tail [])
              (state p middle false true true tail []) := Eval.while_false (by simp)
          have hrun := Eval.while_true hguard hbody hfinish
          refine ⟨(6 * bits.length + 4 + (n + 2)) + 1 + 1, middle, ?_, hmiddle,
            Visits.hit ht heffect, ?_⟩
          · simp only [budget]
            omega
          · simpa [loop, body, unread, ht, tail] using hrun
      | false =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test bits) tail [])
              (afterTag p middle rest suffix) := by
            rw [ht]
            apply Eval.ite_false (by simp)
            exact pop_list_eval p middle rest suffix false true
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          obtain ⟨m, next, hm, hnext, hhistory, hrest⟩ := ih middle hmiddle
          have hrun := Eval.while_true hguard hbody hrest
          refine ⟨(6 * bits.length + 4 + (n + 2)) + m + 1, next, ?_, hnext,
            Visits.miss ht heffect hhistory, ?_⟩
          · simp only [budget]
            omega
          · simpa [loop, body, unread, ht] using hrun

/-- The effect-sensitive form is useful for map/filter/fold builders. -/
theorem iterate_run_with {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (effect : List Bool → State r s → State r s → Prop)
    (contract : CallbackContractWith p callback test cost invariant effect)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (valid : invariant base) (v pr f : Bool) :
    ∃ (n : ℕ) (next : State r s), n ≤ 3 + budget cost records ∧ invariant next ∧
      Visits test effect records base next ∧
      Eval (iterate p callback) n
        (state p base v pr f (Encoding.encodeList id records ++ suffix) [])
        (state p next false true (records.any test) (unread test records suffix) []) := by
  obtain ⟨n, next, hn, hnext, hhistory, hloop⟩ :=
    loop_run_with p callback test cost invariant effect contract records suffix base valid
  refine ⟨1 + (1 + n), next, by omega, hnext, hhistory, ?_⟩
  exact Eval.seq (set_found_eval p base v pr f false _ [])
    (Eval.seq (pop_list_eval p base records suffix v pr) hloop)

/-- A finite instruction table for the iterator and its fixed callback. -/
abbrev program {r s : ℕ} (p : Ports r s) (callback : Cmd r s) :
    Program r s (StructuredCalls.size (iterate p callback) + 1) :=
  StructuredCalls.compiled (iterate p callback) p.source p.source

theorem program_run {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (contract : CallbackContract p callback test cost invariant)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (valid : invariant base) (v pr f : Bool) :
    ∃ next : State r s, invariant next ∧
      RunsIn (program p callback) (4 + budget cost records)
        ((state p base v pr f (Encoding.encodeList id records ++ suffix) []).withPC
          (some (program p callback).entry))
        ((state p next false true (records.any test) (unread test records suffix) []).withPC none) := by
  obtain ⟨n, next, hn, hnext, hrun⟩ :=
    iterate_run p callback test cost invariant contract records suffix base valid v pr f
  exact ⟨next, hnext, n + 1, by omega,
    StructuredCalls.compiled_halt_trace hrun p.source p.source⟩

theorem budget_eq (cost : List Bool → ℕ) (records : List (List Bool)) :
    budget cost records = 6 * (records.map List.length).sum +
      (records.map cost).sum + 7 * records.length := by
  induction records with
  | nil => simp [budget]
  | cons bits rest ih => simp [budget, ih]; omega

theorem budget_le_linear (cost : List Bool → ℕ) (records : List (List Bool))
    (a b : ℕ) (h : ∀ bits ∈ records, cost bits ≤ a * bits.length + b) :
    budget cost records ≤ (a + 6) * (records.map List.length).sum + (b + 7) * records.length := by
  induction records with
  | nil => simp [budget]
  | cons bits rest ih =>
      have hh := h bits (by simp)
      have ht := ih (fun item hi => h item (by simp [hi]))
      simp only [budget, List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

/-- Linear callbacks give a polynomial bound in the actual serialized input,
with all payload bits and record delimiters included. -/
theorem program_budget_le_input (cost : List Bool → ℕ) (records : List (List Bool))
    (a b : ℕ) (h : ∀ bits ∈ records, cost bits ≤ a * bits.length + b) :
    4 + budget cost records ≤
      (a + b + 17) * ((ProgramEncoding.encodeRecords records).length + 1) := by
  have hb := budget_le_linear cost records a b h
  rw [ProgramEncoding.encodeRecords_length]
  let k := a + b + 17
  have hs : (a + 6) * (records.map List.length).sum ≤ k * (records.map List.length).sum :=
    Nat.mul_le_mul_right _ (by dsimp [k]; omega)
  have hr : (b + 7) * records.length ≤ k * records.length :=
    Nat.mul_le_mul_right _ (by dsimp [k]; omega)
  have hfour : 4 ≤ k * 2 := by dsimp [k]; omega
  calc
    4 + budget cost records ≤ k * 2 +
        (k * (records.map List.length).sum + k * records.length) :=
      Nat.add_le_add hfour (hb.trans (Nat.add_le_add hs hr))
    _ = k * ((records.map List.length).sum + records.length + 2) := by ring
    _ ≤ k * (2 * (records.map List.length).sum + 2 * records.length + 1 + 1) :=
      Nat.mul_le_mul_left _ (by omega)

/-- When every callback continues, its auxiliary-state relation folds over
the whole input list in order. This supports exact filter/map output proofs. -/
theorem Visits.fold_of_false {r s : ℕ} {α : Type*}
    {test : List Bool → Bool} {effect : List Bool → State r s → State r s → Prop}
    {records : List (List Bool)} {base next : State r s}
    (h : Visits test effect records base next)
    (never : ∀ bits ∈ records, test bits = false)
    (measure : State r s → α) (update : α → List Bool → α)
    (stepEffect : ∀ bits a b, effect bits a b → measure b = update (measure a) bits) :
    measure next = records.foldl update (measure base) := by
  induction h with
  | nil base => rfl
  | @hit bits rest base next ht he =>
      have hf := never bits (by simp)
      simp [ht] at hf
  | @miss bits rest base middle next ht he hr ih =>
      have hrest : ∀ bits ∈ rest, test bits = false := fun item hi => never item (by simp [hi])
      rw [List.foldl_cons, ← stepEffect bits base middle he]
      exact ih hrest

/-- A typed callback only needs to execute on payloads satisfying its schema. -/
abbrev CallbackContractOn {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (validPayload : List Bool → Prop) : Prop :=
  ∀ (bits tail : List Bool) (base : State r s), validPayload bits → invariant base →
    ∃ (n : ℕ) (next : State r s), n ≤ cost bits ∧ invariant next ∧
      Eval callback n (state p base false true false tail bits.reverse)
        (state p next false true (test bits) tail [])

abbrev CallbackContractWithOn {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (effect : List Bool → State r s → State r s → Prop)
    (validPayload : List Bool → Prop) : Prop :=
  ∀ (bits tail : List Bool) (base : State r s), validPayload bits → invariant base →
    ∃ (n : ℕ) (next : State r s), n ≤ cost bits ∧ invariant next ∧ effect bits base next ∧
      Eval callback n (state p base false true false tail bits.reverse)
        (state p next false true (test bits) tail [])

theorem loop_run_with_on {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (effect : List Bool → State r s → State r s → Prop) (validPayload : List Bool → Prop)
    (contract : CallbackContractWithOn p callback test cost invariant effect validPayload)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (validRecords : ∀ bits ∈ records, validPayload bits) (valid : invariant base) :
    ∃ (n : ℕ) (next : State r s), n ≤ 1 + budget cost records ∧ invariant next ∧
      Visits test effect records base next ∧
      Eval (loop p callback) n (afterTag p base records suffix)
        (state p next false true (records.any test) (unread test records suffix) []) := by
  induction records generalizing base with
  | nil =>
      refine ⟨1, base, by simp [budget], valid, Visits.nil _, ?_⟩
      apply Eval.while_false
      simp [afterTag]
  | cons bits rest ih =>
      let tail := Encoding.encodeList id rest ++ suffix
      obtain ⟨n, middle, hn, hmiddle, heffect, hcallback⟩ :=
        contract bits tail base (validRecords bits (by simp)) valid
      have hreader : Eval (reader p) (6 * bits.length + 4)
          (afterTag p base (bits :: rest) suffix)
          (state p base false true false tail bits.reverse) := by
        simpa [afterTag, tail] using reader_eval p base bits tail [] true true false
      have hguard : (afterTag p base (bits :: rest) suffix).regs p.tag = true := by
        simp [afterTag]
      cases ht : test bits with
      | true =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test bits) tail [])
              (state p middle false true true tail []) := by
            rw [ht]
            apply Eval.ite_true (by simp)
            exact set_tag_eval p middle false true true false tail []
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          have hfinish : Eval (loop p callback) 1
              (state p middle false true true tail [])
              (state p middle false true true tail []) := Eval.while_false (by simp)
          have hrun := Eval.while_true hguard hbody hfinish
          refine ⟨(6 * bits.length + 4 + (n + 2)) + 1 + 1, middle, ?_, hmiddle,
            Visits.hit ht heffect, ?_⟩
          · simp only [budget]
            omega
          · simpa [loop, body, unread, ht, tail] using hrun
      | false =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test bits) tail [])
              (afterTag p middle rest suffix) := by
            rw [ht]
            apply Eval.ite_false (by simp)
            exact pop_list_eval p middle rest suffix false true
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          obtain ⟨m, next, hm, hnext, hhistory, hrest⟩ :=
            ih middle (fun item hi => validRecords item (by simp [hi])) hmiddle
          have hrun := Eval.while_true hguard hbody hrest
          refine ⟨(6 * bits.length + 4 + (n + 2)) + m + 1, next, ?_, hnext,
            Visits.miss ht heffect hhistory, ?_⟩
          · simp only [budget]
            omega
          · simpa [loop, body, unread, ht] using hrun

theorem iterate_run_with_on {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (effect : List Bool → State r s → State r s → Prop) (validPayload : List Bool → Prop)
    (contract : CallbackContractWithOn p callback test cost invariant effect validPayload)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (validRecords : ∀ bits ∈ records, validPayload bits) (valid : invariant base)
    (v pr f : Bool) :
    ∃ (n : ℕ) (next : State r s), n ≤ 3 + budget cost records ∧ invariant next ∧
      Visits test effect records base next ∧
      Eval (iterate p callback) n
        (state p base v pr f (Encoding.encodeList id records ++ suffix) [])
        (state p next false true (records.any test) (unread test records suffix) []) := by
  obtain ⟨n, next, hn, hnext, hhistory, hloop⟩ :=
    loop_run_with_on p callback test cost invariant effect validPayload contract
      records suffix base validRecords valid
  refine ⟨1 + (1 + n), next, by omega, hnext, hhistory, ?_⟩
  exact Eval.seq (set_found_eval p base v pr f false _ [])
    (Eval.seq (pop_list_eval p base records suffix v pr) hloop)

theorem iterate_run_on {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (validPayload : List Bool → Prop)
    (contract : CallbackContractOn p callback test cost invariant validPayload)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (validRecords : ∀ bits ∈ records, validPayload bits) (valid : invariant base)
    (v pr f : Bool) :
    ∃ (n : ℕ) (next : State r s), n ≤ 3 + budget cost records ∧ invariant next ∧
      Eval (iterate p callback) n
        (state p base v pr f (Encoding.encodeList id records ++ suffix) [])
        (state p next false true (records.any test) (unread test records suffix) []) := by
  have hc : CallbackContractWithOn p callback test cost invariant (fun _ _ _ => True) validPayload := by
    intro bits tail state hv hi
    obtain ⟨n, next, hn, hnext, hrun⟩ := contract bits tail state hv hi
    exact ⟨n, next, hn, hnext, trivial, hrun⟩
  obtain ⟨n, next, hn, hnext, _, hrun⟩ := iterate_run_with_on p callback test cost invariant
    (fun _ _ _ => True) validPayload hc records suffix base validRecords valid v pr f
  exact ⟨n, next, hn, hnext, hrun⟩

end SubexponentialSAT.RecordPrograms

end OAI.Algorithms
