import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Encoding
import OAI.Algorithms.SubexponentialSAT.ProgramEncoding
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-!
# Applying a runtime mask to an encoded clause

The mask and clause occupy separate Boolean stacks.  Selection consumes one
mask bit per literal, treating a missing bit as false and leaving excess mask
bits unread.  Payloads are copied as framed bit strings without interpreting
their contents.
-/

namespace SubexponentialSAT.CoreMaskProgram

open SubexponentialSAT.BitProgram
open SubexponentialSAT.StructuredProgram

abbrev Data := StructuredProgram.State 4 4
abbrev Code := StructuredCalls.Cmd 4 4

def select : List Bool → List (List Bool) → List (List Bool)
  | _, [] => []
  | mask, item :: rest =>
      if mask.headD false then item :: select mask.tail rest else select mask.tail rest

theorem select_eq_zip_filterMap (mask : List Bool) (records : List (List Bool)) :
    select mask records =
      (mask.zip records).filterMap (fun p => if p.1 then some p.2 else none) := by
  induction records generalizing mask with
  | nil => simp [select]
  | cons item rest ih =>
      cases mask with
      | nil => simpa [select] using ih []
      | cons b mask => cases b <;> simp [select, ih]

theorem select_sublist (mask : List Bool) (records : List (List Bool)) :
    (select mask records).Sublist records := by
  induction records generalizing mask with
  | nil => exact .slnil
  | cons item rest ih =>
      simp only [select]
      split
      · exact .cons_cons item (ih mask.tail)
      · exact .cons item (ih mask.tail)

theorem select_map_append (p : List Bool → Bool) (records : List (List Bool))
    (suffix : List Bool) :
    select (records.map p ++ suffix) records = records.filter p := by
  induction records with
  | nil => rfl
  | cons item rest ih =>
      cases hp : p item <;> simp [select, hp, ih]

/-- Explicit membership mask, padded to the caller's fixed mask width. -/
def maskForSubset (k : ℕ) (records : List (List Bool)) (H : Finset (List Bool)) : List Bool :=
  records.map (fun item => decide (item ∈ H)) ++ List.replicate (k - records.length) false

theorem maskForSubset_length (k : ℕ) (records : List (List Bool)) (H : Finset (List Bool))
    (hlen : records.length ≤ k) : (maskForSubset k records H).length = k := by
  simp [maskForSubset, Nat.add_sub_of_le hlen]

theorem select_maskForSubset_toFinset (k : ℕ) (records : List (List Bool))
    (H : Finset (List Bool)) (hH : H ⊆ records.toFinset) :
    (select (maskForSubset k records H) records).toFinset = H := by
  unfold maskForSubset
  rw [select_map_append]
  ext item
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun h => ⟨by simpa using hH h, h⟩⟩

theorem exists_mask_of_subset (k : ℕ) (records : List (List Bool))
    (H : Finset (List Bool)) (hlen : records.length ≤ k) (hH : H ⊆ records.toFinset) :
    ∃ mask : List Bool, mask.length = k ∧ (select mask records).toFinset = H :=
  ⟨maskForSubset k records H, maskForSubset_length k records H hlen,
    select_maskForSubset_toFinset k records H hH⟩

def framePrefix : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: framePrefix bs

def recordPrefix : List (List Bool) → List Bool
  | [] => []
  | item :: rest => true :: (Encoding.frame item ++ recordPrefix rest)

theorem frame_eq_prefix (bits : List Bool) :
    Encoding.frame bits = framePrefix bits ++ [false] := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [Encoding.frame_cons, framePrefix, ih]

theorem encode_eq_prefix (records : List (List Bool)) :
    Encoding.encodeList id records = recordPrefix records ++ [false] := by
  induction records with
  | nil => rfl
  | cons item rest ih => simp [Encoding.encodeList, recordPrefix, ih, List.append_assoc]

theorem selected_length_le (mask : List Bool) (records : List (List Bool)) :
    (select mask records).length ≤ records.length := by
  induction records generalizing mask with
  | nil => simp [select]
  | cons item rest ih =>
      simp only [select]
      split
      · simpa using Nat.succ_le_succ (ih mask.tail)
      · exact (ih mask.tail).trans (by simp)

theorem selected_encoded_length_le (mask : List Bool) (records : List (List Bool)) :
    (Encoding.encodeList id (select mask records)).length ≤
      (Encoding.encodeList id records).length := by
  induction records generalizing mask with
  | nil => simp [select]
  | cons item rest ih =>
      simp only [select]
      split
      · simpa only [Encoding.length_encodeList_cons, id_eq] using
          Nat.add_le_add_left (ih mask.tail) (2 * item.length + 2)
      · exact (ih mask.tail).trans (by rw [Encoding.length_encodeList_cons]; omega)

def regs (tag present keep bit : Bool) : Fin 4 → Bool := ![tag, present, keep, bit]
def stackData (source mask accum output : List Bool) : Fin 4 → List Bool :=
  ![source, mask, accum, output]
def state (tag present keep bit : Bool) (source mask accum output : List Bool) : Data :=
  ⟨regs tag present keep bit, stackData source mask accum output⟩

@[simp] theorem stackData_zero (s m a o : List Bool) : stackData s m a o 0 = s := rfl
@[simp] theorem stackData_one (s m a o : List Bool) : stackData s m a o 1 = m := rfl
@[simp] theorem stackData_two (s m a o : List Bool) : stackData s m a o 2 = a := rfl
@[simp] theorem stackData_three (s m a o : List Bool) : stackData s m a o 3 = o := rfl

@[simp] theorem update_regs_zero (t p k b x : Bool) :
    Function.update (regs t p k b) 0 x = regs x p k b := by
  funext j; fin_cases j <;> simp [regs]
@[simp] theorem update_regs_one (t p k b x : Bool) :
    Function.update (regs t p k b) 1 x = regs t x k b := by
  funext j; fin_cases j <;> simp [regs]
@[simp] theorem update_regs_two (t p k b x : Bool) :
    Function.update (regs t p k b) 2 x = regs t p x b := by
  funext j; fin_cases j <;> simp [regs]
@[simp] theorem update_regs_three (t p k b x : Bool) :
    Function.update (regs t p k b) 3 x = regs t p k x := by
  funext j; fin_cases j <;> simp [regs]

@[simp] theorem update_stacks_zero (s m a o x : List Bool) :
    Function.update (stackData s m a o) 0 x = stackData x m a o := by
  funext j; fin_cases j <;> simp [stackData]
@[simp] theorem update_stacks_one (s m a o x : List Bool) :
    Function.update (stackData s m a o) 1 x = stackData s x a o := by
  funext j; fin_cases j <;> simp [stackData]
@[simp] theorem update_stacks_two (s m a o x : List Bool) :
    Function.update (stackData s m a o) 2 x = stackData s m x o := by
  funext j; fin_cases j <;> simp [stackData]
@[simp] theorem update_stacks_three (s m a o x : List Bool) :
    Function.update (stackData s m a o) 3 x = stackData s m a x := by
  funext j; fin_cases j <;> simp [stackData]

def atom (a : StructuredProgram.Atom 4 4) : Code := .base (.atom a)
def popTag : Code := atom (.pop 0 0 1)
def popBit : Code := atom (.pop 0 3 1)
def popMask : Code := atom (.pop 1 2 1)
def emit (r : Fin 4) : Code := .ite 2 (atom (.push 2 r)) (.base .skip)
def emitCost (keep : Bool) : ℕ := if keep then 2 else 1

theorem emitCost_le (keep : Bool) : emitCost keep ≤ 2 := by
  cases keep <;> decide

theorem popTag_eval (t p k d b : Bool) (source mask accum output : List Bool) :
    StructuredCalls.Eval popTag 1
      (state t p k d (b :: source) mask accum output)
      (state b true k d source mask accum output) := by
  apply StructuredCalls.Eval.base
  convert StructuredProgram.Eval.atom (.pop (0 : Fin 4) 0 1)
    (state t p k d (b :: source) mask accum output) using 1
  simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, state, readRegs]

theorem popBit_eval (t p k d b : Bool) (source mask accum output : List Bool) :
    StructuredCalls.Eval popBit 1
      (state t p k d (b :: source) mask accum output)
      (state t true k b source mask accum output) := by
  apply StructuredCalls.Eval.base
  convert StructuredProgram.Eval.atom (.pop (0 : Fin 4) 3 1)
    (state t p k d (b :: source) mask accum output) using 1
  simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, state, readRegs]

theorem popMask_eval (t p k d : Bool) (source mask accum output : List Bool) :
    StructuredCalls.Eval popMask 1 (state t p k d source mask accum output)
      (state t (!mask.isEmpty) (mask.headD false) d source mask.tail accum output) := by
  apply StructuredCalls.Eval.base
  convert StructuredProgram.Eval.atom (.pop (1 : Fin 4) 2 1)
    (state t p k d source mask accum output) using 1
  cases mask <;>
    simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, state, readRegs]

theorem push_eval (r : Fin 4) (t p k d : Bool) (source mask accum output : List Bool) :
    StructuredCalls.Eval (atom (.push 2 r)) 1
      (state t p k d source mask accum output)
      (state t p k d source mask (regs t p k d r :: accum) output) := by
  apply StructuredCalls.Eval.base
  convert StructuredProgram.Eval.atom (.push (2 : Fin 4) r)
    (state t p k d source mask accum output) using 1
  simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, state]

theorem emit_eval (r : Fin 4) (t p k d : Bool) (source mask accum output : List Bool) :
    StructuredCalls.Eval (emit r) (emitCost k)
      (state t p k d source mask accum output)
      (state t p k d source mask
        (if k then regs t p k d r :: accum else accum) output) := by
  cases k with
  | false =>
      exact StructuredCalls.Eval.ite_false rfl (.base (.skip _))
  | true =>
      exact StructuredCalls.Eval.ite_true rfl (push_eval r t p true d source mask accum output)

def frameBody : Code := .seq (emit 0) (.seq popBit (.seq (emit 3) popTag))
def frameLoop : Code := .while 0 frameBody
def scanFrame : Code := .seq popTag (.seq frameLoop (emit 0))

def frameReady (bits tail mask accum output : List Bool) (keep bit : Bool) : Data :=
  match bits with
  | [] => state false true keep bit tail mask accum output
  | b :: bs => state true true keep bit (b :: (Encoding.frame bs ++ tail)) mask accum output

theorem pop_frame_eval (bits tail mask accum output : List Bool) (t p k d : Bool) :
    StructuredCalls.Eval popTag 1
      (state t p k d (Encoding.frame bits ++ tail) mask accum output)
      (frameReady bits tail mask accum output k d) := by
  cases bits with
  | nil => exact popTag_eval t p k d false tail mask accum output
  | cons b bs => exact popTag_eval t p k d true _ mask accum output

theorem frameLoop_eval (bits tail mask accum output : List Bool) (keep bit : Bool) :
    ∃ steps ≤ 7 * bits.length + 1, ∃ last : Bool,
      StructuredCalls.Eval frameLoop steps
        (frameReady bits tail mask accum output keep bit)
        (state false true keep last tail mask
          (if keep then (framePrefix bits).reverse ++ accum else accum) output) := by
  induction bits generalizing accum bit with
  | nil =>
      refine ⟨1, by simp, bit, ?_⟩
      have h : StructuredCalls.Eval frameLoop 1
          (state false true keep bit tail mask accum output)
          (state false true keep bit tail mask accum output) :=
        StructuredCalls.Eval.while_false rfl
      simpa [frameReady, framePrefix] using h
  | cons b bs ih =>
      let a₁ := if keep then true :: accum else accum
      let a₂ := if keep then b :: a₁ else a₁
      have h₁ := emit_eval 0 true true keep bit
        (b :: (Encoding.frame bs ++ tail)) mask accum output
      have h₂ := popBit_eval true true keep bit b
        (Encoding.frame bs ++ tail) mask a₁ output
      have h₃ := emit_eval 3 true true keep b
        (Encoding.frame bs ++ tail) mask a₁ output
      have h₄ := pop_frame_eval bs tail mask a₂ output true true keep b
      have hb : StructuredCalls.Eval frameBody
          (emitCost keep + (1 + (emitCost keep + 1)))
          (frameReady (b :: bs) tail mask accum output keep bit)
          (frameReady bs tail mask a₂ output keep b) :=
        .seq h₁ (.seq h₂ (.seq h₃ h₄))
      obtain ⟨n, hn, last, hi⟩ := ih a₂ b
      have hrun := StructuredCalls.Eval.while_true
        (test := (0 : Fin 4)) (body := frameBody) rfl hb hi
      refine ⟨(emitCost keep + (1 + (emitCost keep + 1))) + n + 1, ?_, last, ?_⟩
      · have he := emitCost_le keep
        simp only [List.length_cons]
        omega
      · convert hrun using 1
        · rfl
        · cases keep <;>
            simp [framePrefix, a₁, a₂, List.reverse_cons, List.append_assoc]

theorem scanFrame_eval (bits tail mask accum output : List Bool) (t p keep bit : Bool) :
    ∃ steps ≤ 7 * bits.length + 4, ∃ last : Bool,
      StructuredCalls.Eval scanFrame steps
        (state t p keep bit (Encoding.frame bits ++ tail) mask accum output)
        (state false true keep last tail mask
          (if keep then (Encoding.frame bits).reverse ++ accum else accum) output) := by
  obtain ⟨n, hn, last, hi⟩ := frameLoop_eval bits tail mask accum output keep bit
  have hp := pop_frame_eval bits tail mask accum output t p keep bit
  have he := emit_eval 0 false true keep last tail mask
    (if keep then (framePrefix bits).reverse ++ accum else accum) output
  have hrun := StructuredCalls.Eval.seq hp (StructuredCalls.Eval.seq hi he)
  refine ⟨1 + (n + emitCost keep), ?_, last, ?_⟩
  · have hc := emitCost_le keep
    omega
  · convert hrun using 1
    · rfl
    · cases keep <;>
        simp [frame_eq_prefix, List.reverse_append, regs]

def recordBody : Code := .seq popMask (.seq (emit 0) (.seq scanFrame popTag))
def recordLoop : Code := .while 0 recordBody
def scanRecords : Code := .seq popTag recordLoop

def recordReady (records : List (List Bool)) (suffix mask accum output : List Bool)
    (keep bit : Bool) : Data :=
  match records with
  | [] => state false true keep bit suffix mask accum output
  | item :: rest => state true true keep bit
      (Encoding.frame item ++ (Encoding.encodeList id rest ++ suffix)) mask accum output

def recordCost (records : List (List Bool)) : ℕ :=
  7 * (records.map List.length).sum + 9 * records.length + 1

theorem pop_record_eval (records : List (List Bool)) (suffix mask accum output : List Bool)
    (t p k d : Bool) :
    StructuredCalls.Eval popTag 1
      (state t p k d (Encoding.encodeList id records ++ suffix) mask accum output)
      (recordReady records suffix mask accum output k d) := by
  cases records with
  | nil => exact popTag_eval t p k d false suffix mask accum output
  | cons item rest =>
      simpa only [Encoding.encodeList, id_eq, List.cons_append, List.append_assoc,
        recordReady] using
        popTag_eval t p k d true
          (Encoding.frame item ++ (Encoding.encodeList id rest ++ suffix)) mask accum output

theorem recordLoop_eval (records : List (List Bool)) (suffix mask accum output : List Bool)
    (keep bit : Bool) :
    ∃ steps ≤ recordCost records, ∃ finalKeep finalBit : Bool,
      StructuredCalls.Eval recordLoop steps
        (recordReady records suffix mask accum output keep bit)
        (state false true finalKeep finalBit suffix (mask.drop records.length)
          ((recordPrefix (select mask records)).reverse ++ accum) output) := by
  induction records generalizing mask accum keep bit with
  | nil =>
      refine ⟨1, by simp [recordCost], keep, bit, ?_⟩
      have h : StructuredCalls.Eval recordLoop 1
          (state false true keep bit suffix mask accum output)
          (state false true keep bit suffix mask accum output) :=
        StructuredCalls.Eval.while_false rfl
      simpa [recordReady, recordPrefix, select] using h
  | cons item rest ih =>
      let chosen := mask.headD false
      let tail := Encoding.encodeList id rest ++ suffix
      let a₁ := if chosen then true :: accum else accum
      let a₂ := if chosen then (Encoding.frame item).reverse ++ a₁ else a₁
      have hm := popMask_eval true true keep bit
        (Encoding.frame item ++ tail) mask accum output
      have he := emit_eval 0 true (!mask.isEmpty) chosen bit
        (Encoding.frame item ++ tail) mask.tail accum output
      obtain ⟨f, hf, middleBit, hframe⟩ :=
        scanFrame_eval item tail mask.tail a₁ output true (!mask.isEmpty) chosen bit
      have hp := pop_record_eval rest suffix mask.tail a₂ output false true chosen middleBit
      have hb : StructuredCalls.Eval recordBody (1 + (emitCost chosen + (f + 1)))
          (recordReady (item :: rest) suffix mask accum output keep bit)
          (recordReady rest suffix mask.tail a₂ output chosen middleBit) :=
        .seq hm (.seq he (.seq hframe hp))
      obtain ⟨n, hn, finalKeep, finalBit, hi⟩ := ih mask.tail a₂ chosen middleBit
      have hrun := StructuredCalls.Eval.while_true
        (test := (0 : Fin 4)) (body := recordBody) rfl hb hi
      refine ⟨(1 + (emitCost chosen + (f + 1))) + n + 1, ?_,
        finalKeep, finalBit, ?_⟩
      · have hc := emitCost_le chosen
        simp only [recordCost, List.map_cons, List.sum_cons, List.length_cons] at *
        omega
      · convert hrun using 1
        · rfl
        · cases mask with
          | nil =>
              simp [select, chosen, a₁, a₂
                 ]
          | cons b mask =>
              cases b <;> simp [select, chosen, a₁, a₂, recordPrefix,
                List.reverse_cons, List.reverse_append, List.append_assoc]

theorem scanRecords_eval (records : List (List Bool))
    (suffix mask accum output : List Bool) (t p keep bit : Bool) :
    ∃ steps ≤ recordCost records + 1, ∃ finalKeep finalBit : Bool,
      StructuredCalls.Eval scanRecords steps
        (state t p keep bit (Encoding.encodeList id records ++ suffix) mask accum output)
        (state false true finalKeep finalBit suffix (mask.drop records.length)
          ((recordPrefix (select mask records)).reverse ++ accum) output) := by
  obtain ⟨n, hn, finalKeep, finalBit, hi⟩ :=
    recordLoop_eval records suffix mask accum output keep bit
  refine ⟨1 + n, by omega, finalKeep, finalBit, ?_⟩
  exact .seq (pop_record_eval records suffix mask accum output t p keep bit) hi

def reverseAccum : Code := .call (StackRoutines.transferProgram 2 3 3 1)
def resetKeep : Code := atom (.set 2 false)

theorem reverseAccum_eval (keep bit : Bool) (suffix mask word : List Bool) :
    StructuredCalls.Eval reverseAccum (3 * word.length + 3)
      (state false true keep bit suffix mask word [])
      (state false false keep false suffix mask [] word.reverse) := by
  apply StructuredCalls.Eval.call
  have h := StackRoutines.transferProgram_trace (2 : Fin 4) 3 (3 : Fin 4) 1
    (by decide) (by decide) (regs false true keep bit) (stackData suffix mask word [])
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  convert hh using 1 <;>
    simp [state, State.withPC,
      StackRoutines.transferResult, StackRoutines.transferStacks, readRegs]

theorem resetKeep_eval (keep : Bool) (suffix mask word : List Bool) :
    StructuredCalls.Eval resetKeep 1
      (state false false keep false suffix mask [] word)
      (state false false false false suffix mask [] word) := by
  apply StructuredCalls.Eval.base
  convert StructuredProgram.Eval.atom (.set (2 : Fin 4) false)
    (state false false keep false suffix mask [] word) using 1
  simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, state]

def command : Code :=
  .seq scanRecords (.seq (atom (.push 2 0)) (.seq reverseAccum resetKeep))

def runtimeBound (records : List (List Bool)) : ℕ :=
  10 * (Encoding.encodeList id records).length + 10

theorem command_eval (records : List (List Bool)) (suffix mask : List Bool)
    (t p keep bit : Bool) :
    ∃ steps, steps + 1 ≤ runtimeBound records ∧
      StructuredCalls.Eval command steps
        (state t p keep bit (Encoding.encodeList id records ++ suffix) mask [] [])
        (state false false false false suffix (mask.drop records.length) []
          (Encoding.encodeList id (select mask records))) := by
  obtain ⟨n, hn, finalKeep, finalBit, hs⟩ :=
    scanRecords_eval records suffix mask [] [] t p keep bit
  let selected := Encoding.encodeList id (select mask records)
  have hword : false :: (recordPrefix (select mask records)).reverse = selected.reverse := by
    simp [selected, encode_eq_prefix, List.reverse_append]
  have hp := push_eval 0 false true finalKeep finalBit suffix (mask.drop records.length)
    (recordPrefix (select mask records)).reverse []
  have hr := reverseAccum_eval finalKeep finalBit suffix (mask.drop records.length) selected.reverse
  have hc := resetKeep_eval finalKeep suffix (mask.drop records.length) selected
  have hs' : StructuredCalls.Eval scanRecords n
      (state t p keep bit (Encoding.encodeList id records ++ suffix) mask [] [])
      (state false true finalKeep finalBit suffix (mask.drop records.length)
        (recordPrefix (select mask records)).reverse []) := by simpa using hs
  have hp' : StructuredCalls.Eval (atom (.push 2 0)) 1
      (state false true finalKeep finalBit suffix (mask.drop records.length)
        (recordPrefix (select mask records)).reverse [])
      (state false true finalKeep finalBit suffix (mask.drop records.length) selected.reverse []) := by
    simpa [regs, hword] using hp
  have hr' : StructuredCalls.Eval reverseAccum (3 * selected.length + 3)
      (state false true finalKeep finalBit suffix (mask.drop records.length) selected.reverse [])
      (state false false finalKeep false suffix (mask.drop records.length) [] selected) := by
    simpa using hr
  refine ⟨n + (1 + ((3 * selected.length + 3) + 1)), ?_,
    .seq hs' (.seq hp' (.seq hr' hc))⟩
  have he := ProgramEncoding.encodeRecords_length records
  have hselect := selected_encoded_length_le mask records
  change (Encoding.encodeList id records).length =
    2 * (records.map List.length).sum + 2 * records.length + 1 at he
  dsimp [recordCost] at hn
  dsimp [runtimeBound, selected]
  omega

def program := StructuredCalls.compiled command (0 : Fin 4) 3

theorem run_correct (records : List (List Bool)) (suffix mask : List Bool)
    (t p keep bit : Bool) :
    BitProgram.RunsIn program (runtimeBound records)
      ((state t p keep bit (Encoding.encodeList id records ++ suffix) mask [] []).withPC
        (some program.entry))
      ((state false false false false suffix (mask.drop records.length) []
        (Encoding.encodeList id (select mask records))).withPC none) := by
  obtain ⟨steps, hsteps, hrun⟩ := command_eval records suffix mask t p keep bit
  exact ⟨steps + 1, hsteps, StructuredCalls.compiled_halt_trace hrun 0 3⟩

theorem call_eval (records : List (List Bool)) (suffix mask : List Bool)
    (t p keep bit : Bool) :
    ∃ steps ≤ runtimeBound records,
      StructuredCalls.Eval (.call program) steps
        (state t p keep bit (Encoding.encodeList id records ++ suffix) mask [] [])
        (state false false false false suffix (mask.drop records.length) []
          (Encoding.encodeList id (select mask records))) := by
  obtain ⟨steps, hsteps, htrace⟩ := run_correct records suffix mask t p keep bit
  exact ⟨steps, hsteps, .call program htrace⟩

theorem primitive_correct (records : List (List Bool)) (suffix mask : List Bool)
    (t p keep bit : Bool) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * runtimeBound records)
      (BitProgram.primitiveCfg program
        ((state t p keep bit (Encoding.encodeList id records ++ suffix) mask [] []).withPC
          (some program.entry)))
      (BitProgram.primitiveCfg program
        ((state false false false false suffix (mask.drop records.length) []
          (Encoding.encodeList id (select mask records))).withPC none)) :=
  BitProgram.primitive_execution program (run_correct records suffix mask t p keep bit)

end SubexponentialSAT.CoreMaskProgram

end OAI.Algorithms
