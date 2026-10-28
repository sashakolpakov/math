import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import OAI.Algorithms.SubexponentialSAT.ExecWorklistProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# Binary-indexed lookup of an encoded clause record

The source is a tagged list of escaped records. The index is a little-endian
Boolean word, with leading zeroes allowed. The finite program copies these two
inputs, decrements the copied index while skipping records, and stops at the
list end marker even if the index is out of range. On success it prepends the
selected record to an arbitrary output suffix. Original inputs are preserved.
-/

namespace SubexponentialSAT.ExecClauseLookupProgram

open BitProgram StructuredCalls
open CounterPrograms (value isZero ripple rippleCost)

abbrev Data := StructuredProgram.State 4 7
abbrev record := ExecWorklistProgram.record
abbrev encode := Encoding.encodeList (id : List Bool → List Bool)

/-- Ports: source, index, output, copied source, copied index, copy scratch,
counter scratch. Registers: value, presence, loop guard, record found. -/
abbrev data (v p go found : Bool) (source index output rest counter : List Bool) : Data :=
  ⟨![v, p, go, found], ![source, index, output, rest, counter, [], []]⟩

private theorem data_ext (a b : Data) (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

private theorem extend_eq {α β γ : Type*} {f : α → β}
    (hf : Function.Injective f) (inner : α → γ) (frame target : β → γ)
    (hin : ∀ i, target (f i) = inner i)
    (hout : ∀ i, (¬ ∃ j, f j = i) → target i = frame i) :
    Function.extend f inner frame = target := by
  classical
  funext i
  by_cases hi : ∃ j, f j = i
  · obtain ⟨j,rfl⟩ := hi
    rw [hf.extend_apply]
    exact (hin j).symm
  · rw [Function.extend_apply' _ _ _ hi]
    exact (hout i hi).symm

theorem embed_eq {r s R S : ℕ} (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (frame target : StructuredProgram.State R S) (inner : StructuredProgram.State r s)
    (hri : ∀ i, target.regs (reg i) = inner.regs i)
    (hro : ∀ i, (¬ ∃ j, reg j = i) → target.regs i = frame.regs i)
    (hsi : ∀ i, target.stacks (stk i) = inner.stacks i)
    (hso : ∀ i, (¬ ∃ j, stk j = i) → target.stacks i = frame.stacks i) :
    embedState reg stk frame inner = target := by
  have he₁ := extend_eq hr inner.regs frame.regs target.regs hri hro
  have he₂ := extend_eq hs inner.stacks frame.stacks target.stacks hsi hso
  cases target
  simp only [embedState, he₁, he₂]

abbrev counterPorts : CounterForPrograms.Ports 4 7 where
  register := ⟨![0, 1, 2], by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  counter := 4
  scratch := 6
  counter_ne_scratch := by decide

theorem install_data (v p go found v' p' go' : Bool)
    (source index output rest counter counter' : List Bool) :
    CounterForPrograms.install counterPorts (data v p go found source index output rest counter)
      v' p' go' counter' [] = data v' p' go' found source index output rest counter' := by
  apply embed_eq _ _ counterPorts.register.injective
    (CounterForPrograms.stackPorts counterPorts).injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨2, rfl⟩)
    · rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;>
      simp_all [ CounterForPrograms.stackPorts ]

def skipRegs : Fin 3 → Fin 4 := ![0, 1, 3]
def skipPorts : Fin 1 → Fin 7 := fun _ => 3
abbrev skipRecord : Cmd 4 7 :=
  .call (ProgramLinking.liftProgram ExecCNFRecords.skipProgram skipRegs skipPorts)

theorem skipRecord_eval (v p go found : Bool)
    (source index output bits rest counter : List Bool) :
    Eval skipRecord (5 * bits.length + 8)
      (data v p go found source index output (record bits ++ rest) counter)
      (data false true go true source index output rest counter) := by
  let a : StructuredProgram.State 3 1 :=
    ⟨ExecCNFRecords.regs v p found, fun _ => record bits ++ rest⟩
  let b : StructuredProgram.State 3 1 :=
    ⟨ExecCNFRecords.regs false true true, fun _ => rest⟩
  have hr : Function.Injective skipRegs := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [skipRegs]
  have hs : Function.Injective skipPorts := fun _ _ _ => Subsingleton.elim _ _
  have ha : embedState skipRegs skipPorts
      (data v p go found source index output (record bits ++ rest) counter) a =
      data v p go found source index output (record bits ++ rest) counter := by
    apply embed_eq _ _ hr hs
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
    · intro i; fin_cases i; rfl
    · intro i hi; rfl
  have hb : embedState skipRegs skipPorts
      (data v p go found source index output (record bits ++ rest) counter) b =
      data false true go true source index output rest counter := by
    apply embed_eq _ _ hr hs
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> simp_all [skipRegs, data, Fin.forall_fin_succ]
    · intro i; fin_cases i; rfl
    · intro i hi; fin_cases i <;> simp_all [skipPorts, data]
  have ht : Trace ExecCNFRecords.skipProgram (5 * bits.length + 8)
      (a.withPC (some ExecCNFRecords.skipProgram.entry)) (b.withPC none) := by
    simpa [a, b, StructuredProgram.State.withPC, ExecCNFRecords.cfg,
      record, ExecWorklistProgram.record] using
      ExecCNFRecords.record_trace bits rest v p found
  have he := eval_call_lifted ExecCNFRecords.skipProgram skipRegs skipPorts
    (data v p go found source index output (record bits ++ rest) counter) hr hs ht
  rw [ha, hb] at he
  exact he

def copyRegs : Fin 2 → Fin 4 := ![0, 1]
def copyPorts : Fin 3 → Fin 7 := ![3, 2, 5]
abbrev emitRecord : Cmd 4 7 :=
  .call (ProgramLinking.liftProgram ExecCNFRecords.copyProgram copyRegs copyPorts)

theorem emitRecord_eval (v p go found : Bool)
    (source index output bits rest counter : List Bool) :
    Eval emitRecord (13 * bits.length + 18)
      (data v p go found source index output (record bits ++ rest) counter)
      (data false false go found source index (record bits ++ output) rest counter) := by
  let a : StructuredProgram.State 2 3 :=
    ⟨ParserProgram.pair v p, ExecCNFRecords.ports (record bits ++ rest) output []⟩
  let b : StructuredProgram.State 2 3 :=
    ⟨ParserProgram.pair false false, ExecCNFRecords.ports rest (record bits ++ output) []⟩
  have hr : Function.Injective copyRegs := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [copyRegs]
  have hs : Function.Injective copyPorts := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [copyPorts]
  have ha : embedState copyRegs copyPorts
      (data v p go found source index output (record bits ++ rest) counter) a =
      data v p go found source index output (record bits ++ rest) counter := by
    apply embed_eq _ _ hr hs
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  have hb : embedState copyRegs copyPorts
      (data v p go found source index output (record bits ++ rest) counter) b =
      data false false go found source index (record bits ++ output) rest counter := by
    apply embed_eq _ _ hr hs
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> simp_all [copyRegs, data ]
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> simp_all [copyPorts, data, Fin.forall_fin_succ]
  have ht : Trace ExecCNFRecords.copyProgram (13 * bits.length + 18)
      (a.withPC (some ExecCNFRecords.copyProgram.entry)) (b.withPC none) := by
    simpa [a, b, StructuredProgram.State.withPC, ExecCNFRecords.copyCfg,
      record, ExecWorklistProgram.record] using
      ExecCNFRecords.copy_record_trace bits rest output v p
  have he := eval_call_lifted ExecCNFRecords.copyProgram copyRegs copyPorts
    (data v p go found source index output (record bits ++ rest) counter) hr hs ht
  rw [ha, hb] at he
  exact he

abbrev atom (a : StructuredProgram.Atom 4 7) : Cmd 4 7 := .base (.atom a)

abbrev test : Cmd 4 7 :=
  .seq (CounterForPrograms.zeroCmd counterPorts)
    (.seq (atom (.peek 3 3 1)) (.seq (atom (.bnot 2 2)) (atom (.band 2 2 3))))

def ready (source index output : List Bool) (records : List (List Bool))
    (counter : List Bool) : Data :=
  data false true ((!isZero counter) && !records.isEmpty) (!records.isEmpty)
    source index output (encode records) counter

theorem test_eval (v p go found : Bool) (source index output : List Bool)
    (records : List (List Bool)) (counter : List Bool) :
    Eval test (8 * counter.length + 9)
      (data v p go found source index output (encode records) counter)
      (ready source index output records counter) := by
  have hz := CounterForPrograms.zero_eval counterPorts
    (data v p go found source index output (encode records) counter) rfl
  change Eval _ (8 * counter.length + 6) _ _ at hz
  change Eval _ _ _ (CounterForPrograms.install counterPorts _ false false
    (isZero counter) counter []) at hz
  rw [install_data] at hz
  have he := Eval.seq hz (Eval.seq
    (Eval.base (StructuredProgram.Eval.atom (.peek 3 3 1) _))
    (Eval.seq (Eval.base (StructuredProgram.Eval.atom (.bnot 2 2) _))
      (Eval.base (StructuredProgram.Eval.atom (.band 2 2 3) _))))
  convert he using 1 ; first
    | (simp only [data]; omega)
    | (cases records <;> apply data_ext <;> funext i <;> fin_cases i <;>
        simp [ready, data, encode, Encoding.encodeList, StructuredProgram.Atom.eval,
          StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs])

abbrev body : Cmd 4 7 :=
  .seq skipRecord (.seq (CounterForPrograms.decrementCmd counterPorts) test)

abbrev loop : Cmd 4 7 := .while 2 body

/-- This finite specification follows the actual bounded record scan. -/
def seek : List (List Bool) → List Bool → List (List Bool) × List Bool
  | [], counter => ([], counter)
  | x :: xs, counter => if isZero counter then (x :: xs, counter)
      else seek xs (ripple false counter)

def loopCost : List (List Bool) → List Bool → ℕ
  | [], _ => 1
  | x :: xs, counter => if isZero counter then 1 else
      (5 * x.length + 8) + (rippleCost false counter + 1) +
        (8 * (ripple false counter).length + 9) + loopCost xs (ripple false counter) + 1

theorem body_eval (source index output x : List Bool) (xs : List (List Bool))
    (counter : List Bool) (hzero : isZero counter = false) :
    Eval body ((5 * x.length + 8) + (rippleCost false counter + 1) +
      (8 * (ripple false counter).length + 9))
      (ready source index output (x :: xs) counter)
      (ready source index output xs (ripple false counter)) := by
  have hs := skipRecord_eval false true true true source index output x (encode xs) counter
  have hd := CounterForPrograms.decrement_eval counterPorts
    (data false true true true source index output (encode xs) counter) rfl
  change Eval _ _ _ (CounterForPrograms.install counterPorts _ false false true
    (ripple false counter) []) at hd
  rw [install_data] at hd
  have ht := test_eval false false true true source index output xs (ripple false counter)
  have he := Eval.seq hs (Eval.seq hd ht)
  simpa [body, ready, encode, Encoding.encodeList, record, ExecWorklistProgram.record,
    hzero, Nat.add_assoc] using he

theorem loop_eval (source index output : List Bool) (records : List (List Bool))
    (counter : List Bool) :
    Eval loop (loopCost records counter) (ready source index output records counter)
      (ready source index output (seek records counter).1 (seek records counter).2) := by
  induction records generalizing counter with
  | nil => exact Eval.while_false (by simp [ready, data])
  | cons x xs ih =>
      cases hz : isZero counter with
      | true => simpa [loopCost, seek, hz] using
          (Eval.while_false (body := body) (by simp [ready, data, hz] :
            (ready source index output (x :: xs) counter).regs 2 = false))
      | false =>
          have he := Eval.while_true
            (by simp [ready, data, hz] : (ready source index output (x :: xs) counter).regs 2 = true)
            (body_eval source index output x xs counter hz) (ih (ripple false counter))
          simpa [loop, loopCost, seek, hz] using he

theorem seek_head (records : List (List Bool)) (counter : List Bool) :
    (seek records counter).1.head? = records[value counter]? := by
  induction records generalizing counter with
  | nil => simp [seek]
  | cons x xs ih =>
      cases hz : isZero counter with
      | true =>
          have hv := (CounterPrograms.isZero_eq_true_iff counter).mp hz
          simp [seek, hz, hv]
      | false =>
          have hp := (CounterPrograms.isZero_eq_false_iff counter).mp hz
          have hd := CounterPrograms.value_decrement hp
          simpa [seek, hz, ← hd] using ih (ripple false counter)

theorem seek_counter_length (records : List (List Bool)) (counter : List Bool) :
    (seek records counter).2.length = counter.length := by
  induction records generalizing counter with
  | nil => rfl
  | cons x xs ih =>
      cases hz : isZero counter with
      | true => simp [seek, hz]
      | false =>
          have hp := (CounterPrograms.isZero_eq_false_iff counter).mp hz
          simp [seek, hz, ih, CounterPrograms.decrement_length hp]

theorem seek_encoded_length (records : List (List Bool)) (counter : List Bool) :
    (encode (seek records counter).1).length ≤ (encode records).length := by
  induction records generalizing counter with
  | nil => exact le_rfl
  | cons x xs ih =>
      cases hz : isZero counter with
      | true => simp [seek, hz]
      | false =>
          have hi := ih (ripple false counter)
          simp only [seek, hz, Bool.false_eq_true, ↓reduceIte]
          exact hi.trans (by simp only [encode, Encoding.length_encodeList_cons]; omega)

/-- The scan is bounded by encoded input size and index word length, even when
the represented index is much larger than the number of records. -/
theorem loopCost_le (records : List (List Bool)) (counter : List Bool) :
    loopCost records counter ≤ 20 * ((encode records).length + 1) * (counter.length + 1) := by
  induction records generalizing counter with
  | nil => simp [loopCost, encode, Encoding.encodeList]; omega
  | cons x xs ih =>
      cases hz : isZero counter with
      | true =>
          simp only [loopCost, hz, ↓reduceIte]
          have hp : 0 < 20 * ((encode (x :: xs)).length + 1) * (counter.length + 1) := by positivity
          omega
      | false =>
          have hp := (CounterPrograms.isZero_eq_false_iff counter).mp hz
          have hl := CounterPrograms.decrement_length hp
          have hc := CounterPrograms.rippleCost_le false counter
          have hi := ih (ripple false counter)
          rw [hl] at hi
          simp only [loopCost, hz, Bool.false_eq_true, ↓reduceIte, hl,
            encode, Encoding.length_encodeList_cons]
          change loopCost xs (ripple false counter) ≤
            20 * ((encode xs).length + 1) * (counter.length + 1) at hi
          simp only [encode, id_eq] at hi ⊢
          nlinarith [Nat.zero_le (x.length * counter.length)]

abbrev clearRest : Cmd 4 7 := .call (StackRoutines.clearProgram 3 0 1)
abbrev clearCounter : Cmd 4 7 := .call (StackRoutines.clearProgram 4 0 1)

theorem clearRest_eval (v p go found : Bool)
    (source index output rest counter : List Bool) :
    Eval clearRest (2 * rest.length + 3)
      (data v p go found source index output rest counter)
      (data false false go found source index output [] counter) := by
  have he : Eval clearRest (2 * rest.length + 3)
      (data v p go found source index output rest counter)
      ⟨readRegs (data v p go found source index output rest counter).regs 0 1 none,
        StackRoutines.clearStacks 3
          (data v p go found source index output rest counter).stacks⟩ :=
    Eval.call _ (by
      simpa [StackRoutines.clearProgram] using ListRegisterProgram.clear_run (r := 4) (s := 7) 3 0 1
        (data v p go found source index output rest counter).regs
        (data v p go found source index output rest counter).stacks)
  convert he using 1
  apply data_ext <;> funext i <;> fin_cases i <;> simp [ readRegs, StackRoutines.clearStacks]

theorem clearCounter_eval (v p go found : Bool)
    (source index output rest counter : List Bool) :
    Eval clearCounter (2 * counter.length + 3)
      (data v p go found source index output rest counter)
      (data false false go found source index output rest []) := by
  have he : Eval clearCounter (2 * counter.length + 3)
      (data v p go found source index output rest counter)
      ⟨readRegs (data v p go found source index output rest counter).regs 0 1 none,
        StackRoutines.clearStacks 4
          (data v p go found source index output rest counter).stacks⟩ :=
    Eval.call _ (by
      simpa [StackRoutines.clearProgram] using ListRegisterProgram.clear_run (r := 4) (s := 7) 4 0 1
        (data v p go found source index output rest counter).regs
        (data v p go found source index output rest counter).stacks)
  convert he using 1
  apply data_ext <;> funext i <;> fin_cases i <;> simp [ readRegs, StackRoutines.clearStacks]

abbrev finish : Cmd 4 7 :=
  .seq (.ite 3 emitRecord (.base .skip))
    (.seq clearRest (.seq clearCounter (atom (.set 2 false))))

def prependResult (item : Option (List Bool)) (output : List Bool) : List Bool :=
  match item with
  | none => output
  | some bits => record bits ++ output

def finishCost (records : List (List Bool)) (counter : List Bool) : ℕ :=
  match records with
  | [] => 1 + (2 * (encode []).length + 3) + (2 * counter.length + 3) + 1
  | bits :: rest => (13 * bits.length + 18 + 1) +
      (2 * (encode rest).length + 3) + (2 * counter.length + 3) + 1

theorem finish_eval (source index output : List Bool) (records : List (List Bool))
    (counter : List Bool) :
    Eval finish (finishCost records counter) (ready source index output records counter)
      (data false false false (!records.isEmpty) source index
        (prependResult records.head? output) [] []) := by
  cases records with
  | nil =>
      have hfirst : Eval (.ite 3 emitRecord (.base .skip)) 1
          (ready source index output [] counter) (ready source index output [] counter) :=
        Eval.ite_false rfl (Eval.base (StructuredProgram.Eval.skip _))
      have hclear := clearRest_eval false true false false source index output (encode []) counter
      have hcount := clearCounter_eval false false false false source index output [] counter
      have hset := Eval.base (StructuredProgram.Eval.atom (.set 2 false)
        (data false false false false source index output [] []))
      simp only [ready, List.isEmpty_nil, Bool.not_true, Bool.and_false] at hfirst
      have he := Eval.seq hfirst (Eval.seq hclear (Eval.seq hcount hset))
      convert he using 1 <;> first
        | (simp only [finishCost]; omega)
        | (apply data_ext <;> funext i <;> fin_cases i <;>
            simp [ready, prependResult, data, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
              StructuredProgram.State.ofCfg, execInstr])
  | cons bits rest =>
      let go := !isZero counter
      have hfirst : Eval (.ite 3 emitRecord (.base .skip)) (13 * bits.length + 18 + 1)
          (ready source index output (bits :: rest) counter)
          (data false false go true source index (record bits ++ output) (encode rest) counter) := by
        apply Eval.ite_true rfl
        simpa [ready, go, encode, Encoding.encodeList, record, ExecWorklistProgram.record] using
          emitRecord_eval false true go true source index output bits (encode rest) counter
      have hclear := clearRest_eval false false go true source index
        (record bits ++ output) (encode rest) counter
      have hcount := clearCounter_eval false false go true source index (record bits ++ output) [] counter
      have hset := Eval.base (StructuredProgram.Eval.atom (.set 2 false)
        (data false false go true source index (record bits ++ output) [] []))
      have he := Eval.seq hfirst (Eval.seq hclear (Eval.seq hcount hset))
      convert he using 1 <;> first
        | (simp only [finishCost]; omega)
        | (apply data_ext <;> funext i <;> fin_cases i <;>
            simp [ prependResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
              StructuredProgram.State.ofCfg, execInstr])

abbrev copySource : Cmd 4 7 := .call (StackRoutines.copyProgram 0 3 5 0 1)
abbrev copyIndex : Cmd 4 7 := .call (StackRoutines.copyProgram 1 4 5 0 1)

theorem copySource_eval (v p go found : Bool) (source index output : List Bool) :
    Eval copySource (7 * source.length + 5)
      (data v p go found source index output [] [])
      (data false false go found source index output source []) := by
  have he : Eval copySource (7 * source.length + 5)
      (data v p go found source index output [] [])
      ⟨readRegs (data v p go found source index output [] []).regs 0 1 none,
        StackRoutines.copyStacks 0 3 (data v p go found source index output [] []).stacks⟩ :=
    Eval.call _ (by
      simpa [StackRoutines.copyProgram] using ListRegisterProgram.copy_run (r := 4) (s := 7) 0 3 5 0 1
        (by decide) (by decide) (by decide) (by decide)
        (data v p go found source index output [] []).regs
        (data v p go found source index output [] []).stacks rfl)
  convert he using 1
  apply data_ext <;> funext i <;> fin_cases i <;> simp [ readRegs, StackRoutines.copyStacks]

theorem copyIndex_eval (v p go found : Bool) (source index output rest : List Bool) :
    Eval copyIndex (7 * index.length + 5)
      (data v p go found source index output rest [])
      (data false false go found source index output rest index) := by
  have he : Eval copyIndex (7 * index.length + 5)
      (data v p go found source index output rest [])
      ⟨readRegs (data v p go found source index output rest []).regs 0 1 none,
        StackRoutines.copyStacks 1 4 (data v p go found source index output rest []).stacks⟩ :=
    Eval.call _ (by
      simpa [StackRoutines.copyProgram] using ListRegisterProgram.copy_run (r := 4) (s := 7) 1 4 5 0 1
        (by decide) (by decide) (by decide) (by decide)
        (data v p go found source index output rest []).regs
        (data v p go found source index output rest []).stacks rfl)
  convert he using 1
  apply data_ext <;> funext i <;> fin_cases i <;> simp [ readRegs, StackRoutines.copyStacks]

abbrev command : Cmd 4 7 :=
  .seq copySource (.seq copyIndex (.seq test (.seq loop finish)))

/-- One fixed table; all record lengths and index values are runtime data. -/
abbrev program := compiled command 0 2

def cost (records : List (List Bool)) (index : List Bool) : ℕ :=
  (7 * (encode records).length + 5) + (7 * index.length + 5) +
    (8 * index.length + 9) + loopCost records index +
      finishCost (seek records index).1 (seek records index).2

theorem command_eval (v p go found : Bool) (records : List (List Bool))
    (index output : List Bool) :
    Eval command (cost records index)
      (data v p go found (encode records) index output [] [])
      (data false false false (records[value index]?).isSome
        (encode records) index (prependResult (records[value index]?) output) [] []) := by
  have hs := copySource_eval v p go found (encode records) index output
  have hi := copyIndex_eval false false go found (encode records) index output (encode records)
  have ht := test_eval false false go found (encode records) index output records index
  have hl := loop_eval (encode records) index output records index
  have hf := finish_eval (encode records) index output (seek records index).1 (seek records index).2
  have he := Eval.seq hs (Eval.seq hi (Eval.seq ht (Eval.seq hl hf)))
  have hfound : (!(seek records index).1.isEmpty) = (records[value index]?).isSome := by
    rw [← seek_head]
    cases (seek records index).1 <;> rfl
  rw [hfound] at he
  simpa only [command, cost, Nat.add_assoc, seek_head] using he

theorem finishCost_le (records : List (List Bool)) (counter : List Bool) :
    finishCost records counter ≤ 13 * (encode records).length + 2 * counter.length + 10 := by
  cases records with
  | nil => simp [finishCost, encode, Encoding.encodeList]; omega
  | cons x xs =>
      simp only [finishCost, encode, Encoding.length_encodeList_cons, id_eq]
      omega

theorem cost_le (records : List (List Bool)) (index : List Bool) :
    cost records index + 1 ≤ 64 * ((encode records).length + 1) * (index.length + 1) := by
  have hl := loopCost_le records index
  have hf := finishCost_le (seek records index).1 (seek records index).2
  have hs := seek_encoded_length records index
  rw [seek_counter_length] at hf
  unfold cost
  nlinarith [Nat.zero_le ((encode records).length * index.length)]

/-- Correctness for arbitrary binary words and arbitrary accumulated output.
Out-of-range indices leave the output unchanged and return `found = false`. -/
theorem program_trace (v p go found : Bool) (records : List (List Bool))
    (index output : List Bool) :
    Trace program (cost records index + 1)
      ((data v p go found (encode records) index output [] []).withPC (some program.entry))
      ((data false false false (records[value index]?).isSome
        (encode records) index (prependResult (records[value index]?) output) [] []).withPC none) :=
  compiled_halt_trace (command_eval v p go found records index output) 0 2

theorem program_runs (v p go found : Bool) (records : List (List Bool))
    (index output : List Bool) :
    RunsIn program (64 * ((encode records).length + 1) * (index.length + 1))
      ((data v p go found (encode records) index output [] []).withPC (some program.entry))
      ((data false false false (records[value index]?).isSome
        (encode records) index (prependResult (records[value index]?) output) [] []).withPC none) :=
  ⟨cost records index + 1, cost_le records index, program_trace v p go found records index output⟩

theorem program_primitive (v p go found : Bool) (records : List (List Bool))
    (index output : List Bool) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program *
        (64 * ((encode records).length + 1) * (index.length + 1)))
      (BitProgram.primitiveCfg program
        ((data v p go found (encode records) index output [] []).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((data false false false (records[value index]?).isSome
          (encode records) index (prependResult (records[value index]?) output) [] []).withPC none)) :=
  (BitProgram.primitive_trace program (program_trace v p go found records index output)).mono
    (Nat.mul_le_mul_left _ (cost_le records index))

theorem encode_map {α : Type*} (f : α → List Bool) (xs : List α) :
    encode (xs.map f) = Encoding.encodeList f xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encode, Encoding.encodeList, ih]

/-- Instantiation for a CNF whose literals themselves are Boolean words. -/
theorem clause_trace (v p go found : Bool) (formula : List (List (List Bool)))
    (index output : List Bool) :
    Trace program (cost (formula.map encode) index + 1)
      ((data v p go found (Encoding.encodeList encode formula) index output [] []).withPC
        (some program.entry))
      ((data false false false ((formula[value index]?).map encode).isSome
        (Encoding.encodeList encode formula) index
        (prependResult ((formula[value index]?).map encode) output) [] []).withPC none) := by
  simpa only [encode_map, List.getElem?_map] using
    program_trace v p go found (formula.map encode) index output

end SubexponentialSAT.ExecClauseLookupProgram

end OAI.Algorithms
