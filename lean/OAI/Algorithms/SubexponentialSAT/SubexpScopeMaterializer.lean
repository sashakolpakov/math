import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCandidateMaterializer
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# Canonical scope-record iteration for candidate materialization

Scope indices use the existing `encodeList encodeNat` format. Candidate labels
form a flat stream of equally sized little-endian records. The record reader,
label extraction, chunk update, and validity accumulation are actual finite
programs; the list functions below specify their result.
-/

namespace SubexponentialSAT.SubexpScopeMaterializer

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StackRoutines SubexponentialSAT.ArrayPrograms SubexponentialSAT.SubexpFactorProgram

abbrev Data := StructuredProgram.State 6 18

def registers (tag present : Bool) : Fin 6 → Bool :=
  ![false, false, false, tag, present, false]

/-- Local materializer ports 0–9; scope 10; flat labels 11; unary record width 12;
label-extraction scratch 13–15; parsed payload 16; aggregate validity 17. -/
def tapes (array replacement index ell label valid scope labels width counter temporary reversed
    payload aggregate : List Bool) : Fin 18 → List Bool :=
  ![array, replacement, index, ell, [], [], [], [], label, valid,
    scope, labels, width, counter, temporary, reversed, payload, aggregate]

private theorem tapes_eq (array replacement index ell label valid scope labels width counter
    temporary reversed payload aggregate : List Bool) :
    tapes array replacement index ell label valid scope labels width counter temporary reversed
      payload aggregate = fun i =>
      if i = 0 then array else if i = 1 then replacement else
      if i = 2 then index else if i = 3 then ell else
      if i = 8 then label else if i = 9 then valid else
      if i = 10 then scope else if i = 11 then labels else
      if i = 12 then width else if i = 13 then counter else
      if i = 14 then temporary else if i = 15 then reversed else
      if i = 16 then payload else if i = 17 then aggregate else [] := by
  funext i
  fin_cases i <;> rfl

def data (tag present : Bool) (array replacement index ell label valid scope labels width counter
    temporary reversed payload aggregate : List Bool) : Data :=
  ⟨registers tag present,
    tapes array replacement index ell label valid scope labels width counter temporary reversed
      payload aggregate⟩

def resting (tag present : Bool) (array ell scope labels width : List Bool) (valid : Bool) : Data :=
  data tag present array [] [] ell [] [] scope labels width [] [] [] [] [valid]

private theorem state_ext {r s : ℕ} {a b : StructuredProgram.State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

private theorem read_reset (tag present : Bool) :
    readRegs (registers tag present) 0 1 none = registers tag present := by
  funext i; fin_cases i <;> simp [registers, readRegs]

private theorem copy_eval {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (ht : stk tmp = []) :
    StructuredCalls.Eval (.call (copyProgram src dst tmp value present))
      (7 * (stk src).length + 5) ⟨regs, stk⟩
      ⟨readRegs regs value present none, copyStacks src dst stk⟩ :=
  .call _ (ListRegisterProgram.copy_run src dst tmp value present hsd hst htd hvp regs stk ht)

private theorem transfer_eval {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    StructuredCalls.Eval (.call (transferProgram src dst value present))
      (3 * (stk src).length + 3) ⟨regs, stk⟩
      ⟨readRegs regs value present none, transferStacks src dst stk⟩ :=
  .call _ (ListRegisterProgram.transfer_run src dst value present hsd hvp regs stk)

private theorem countedTransfer_eval {r s : ℕ} (counter src dst : Fin s)
    (value present : Fin r) (hcs : counter ≠ src) (hcd : counter ≠ dst)
    (hsd : src ≠ dst) (hvp : value ≠ present)
    (segment rest countWord : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : stk src = segment ++ rest) (hc : stk counter = countWord)
    (hlen : countWord.length = segment.length) :
    StructuredCalls.Eval (.call (countedTransferProgram counter src dst value present))
      (4 * segment.length + 3) ⟨regs, stk⟩
      ⟨readRegs regs value present none, countedTransferStacks counter src dst segment rest stk⟩ := by
  apply StructuredCalls.Eval.call
  have h := halt_after_trace _ (countedTransferProgram_trace counter src dst value present
    hcs hcd hsd hvp segment rest countWord regs stk hs hc hlen) 4 rfl rfl
  simpa [State.withPC, countedTransferResult, countedTransferProgram, Nat.add_assoc] using h

abbrev decodeIndex : StructuredCalls.Cmd 6 18 :=
  .seq (.base (.atom (.pop 16 0 1))) (.call (transferProgram 16 2 0 1))

theorem decodeIndex_eval (j : ℕ) (array ell scope labels width : List Bool) (valid : Bool) :
    StructuredCalls.Eval decodeIndex (3 * j + 4)
      (data false true array [] [] ell [] [] scope labels width [] [] []
        (Encoding.encodeNat j).reverse [valid])
      (data false true array [] (List.replicate j true) ell [] [] scope labels width [] [] [] []
        [valid]) := by
  let start := data false true array [] [] ell [] [] scope labels width [] [] []
    (Encoding.encodeNat j).reverse [valid]
  let mid := (StructuredProgram.Atom.pop (16 : Fin 18) (0 : Fin 6) 1).eval start
  have hp : StructuredCalls.Eval (.base (.atom (.pop 16 0 1))) 1 start mid :=
    .base (.atom _ _)
  have ht := transfer_eval (16 : Fin 18) 2 (0 : Fin 6) 1 (by decide) (by decide)
    mid.regs mid.stacks
  have hm : (mid.stacks 16).length = j := by
    simp [mid, start, data, tapes, Atom.eval, Atom.instr, State.ofCfg,
      execInstr, Encoding.encodeNat, List.reverse_append]
  have heq : (⟨readRegs mid.regs 0 1 none, transferStacks 16 2 mid.stacks⟩ : Data) =
      data false true array [] (List.replicate j true) ell [] [] scope labels width [] [] [] []
        [valid] := by
    apply state_ext
    · funext i; fin_cases i <;>
        simp [mid, start, data, registers, Atom.eval, Atom.instr, State.ofCfg,
          execInstr, readRegs, tapes, Encoding.encodeNat, List.reverse_append]
    · funext i; fin_cases i <;>
        simp [mid, start, data, tapes, Atom.eval, Atom.instr, State.ofCfg,
          execInstr, transferStacks, Encoding.encodeNat, List.reverse_append]
  have h := hp.seq ht
  simpa only [decodeIndex, hm, heq, Nat.add_comm 1] using h

abbrev copyRecordWidth : StructuredCalls.Cmd 6 18 := .call (copyProgram 12 13 14 0 1)
abbrev takeRecord : StructuredCalls.Cmd 6 18 := .call (countedTransferProgram 13 11 15 0 1)
abbrev restoreRecord : StructuredCalls.Cmd 6 18 := .call (transferProgram 15 8 0 1)

theorem copyRecordWidth_eval (array index ell scope labels width : List Bool) (valid : Bool) :
    StructuredCalls.Eval copyRecordWidth (7 * width.length + 5)
      (data false true array [] index ell [] [] scope labels width [] [] [] [] [valid])
      (data false true array [] index ell [] [] scope labels width width [] [] [] [valid]) := by
  have hstore : copyStacks (12 : Fin 18) 13
      (tapes array [] index ell [] [] scope labels width [] [] [] [] [valid]) =
      tapes array [] index ell [] [] scope labels width width [] [] [] [valid] := by
    funext i; fin_cases i <;> simp [copyStacks, tapes]
  have h := copy_eval (12 : Fin 18) 13 14 (0 : Fin 6) 1
    (by decide) (by decide) (by decide) (by decide) (registers false true)
    (tapes array [] index ell [] [] scope labels width [] [] [] [] [valid]) rfl
  rw [hstore] at h
  have hwidth : (tapes array [] index ell [] [] scope labels width [] [] [] [] [valid]) 12 =
      width := by simp [tapes]
  rw [read_reset] at h
  simpa only [hwidth, copyRecordWidth, data] using h

theorem takeRecord_eval (array index ell scope label labels width : List Bool) (valid : Bool)
    (hw : width.length = label.length) :
    StructuredCalls.Eval takeRecord (4 * label.length + 3)
      (data false true array [] index ell [] [] scope (label ++ labels) width width [] [] [] [valid])
      (data false true array [] index ell [] [] scope labels width [] [] label.reverse [] [valid]) := by
  have hstore : countedTransferStacks (13 : Fin 18) 11 15 label labels
      (tapes array [] index ell [] [] scope (label ++ labels) width width [] [] [] [valid]) =
      tapes array [] index ell [] [] scope labels width [] [] label.reverse [] [valid] := by
    funext i; fin_cases i <;> simp [countedTransferStacks, tapes]
  have h := countedTransfer_eval (13 : Fin 18) 11 15 (0 : Fin 6) 1
    (by decide) (by decide) (by decide) (by decide) label labels width (registers false true)
    (tapes array [] index ell [] [] scope (label ++ labels) width width [] [] [] [valid])
    rfl rfl hw
  simpa only [takeRecord, data, hstore, read_reset] using h

theorem restoreRecord_eval (array index ell scope label labels width : List Bool) (valid : Bool) :
    StructuredCalls.Eval restoreRecord (3 * label.length + 3)
      (data false true array [] index ell [] [] scope labels width [] [] label.reverse [] [valid])
      (data false true array [] index ell label [] scope labels width [] [] [] [] [valid]) := by
  have hstore : transferStacks (15 : Fin 18) 8
      (tapes array [] index ell [] [] scope labels width [] [] label.reverse [] [valid]) =
      tapes array [] index ell label [] scope labels width [] [] [] [] [valid] := by
    funext i; fin_cases i <;> simp [transferStacks, tapes]
  have h := transfer_eval (15 : Fin 18) 8 (0 : Fin 6) 1 (by decide) (by decide)
    (registers false true)
    (tapes array [] index ell [] [] scope labels width [] [] label.reverse [] [valid])
  have hl : (tapes array [] index ell [] [] scope labels width [] [] label.reverse [] [valid] 15).length =
      label.length := by
    change label.reverse.length = label.length
    simp
  rw [hl] at h
  simpa only [restoreRecord, data, hstore, read_reset, List.length_reverse] using h

abbrev extractRecord : StructuredCalls.Cmd 6 18 :=
  .seq copyRecordWidth (.seq takeRecord restoreRecord)

theorem extractRecord_eval (array index ell scope label labels width : List Bool) (valid : Bool)
    (hw : label.length = width.length) :
    StructuredCalls.Eval extractRecord (14 * width.length + 11)
      (data false true array [] index ell [] [] scope (label ++ labels) width [] [] [] [] [valid])
      (data false true array [] index ell label [] scope labels width [] [] [] [] [valid]) := by
  have h := (copyRecordWidth_eval array index ell scope (label ++ labels) width valid).seq
    ((takeRecord_eval array index ell scope label labels width valid hw.symm).seq
      (restoreRecord_eval array index ell scope label labels width valid))
  convert h using 1 ; simp only [hw] ; ring

def patchRegisters (i : Fin 3) : Fin 6 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
def patchStacks (i : Fin 10) : Fin 18 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
theorem patchRegisters_injective : Function.Injective patchRegisters := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 6 => k.val) h)
theorem patchStacks_injective : Function.Injective patchStacks := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 18 => k.val) h)

abbrev patch : StructuredCalls.Cmd 6 18 :=
  .call (ProgramLinking.liftProgram SubexpCandidateMaterializer.program patchRegisters patchStacks)

private theorem embed_patch (array replacement index ell label valid scope labels width aggregate :
    List Bool) :
    StructuredCalls.embedState patchRegisters patchStacks
      (data false true [] [] [] [] [] [] scope labels width [] [] [] [] aggregate)
      (SubexpCandidateMaterializer.state array replacement index ell [] [] [] [] label valid) =
      data false true array replacement index ell label valid scope labels width [] [] [] []
        aggregate := by
  apply StructuredCalls.embedState_eq_of_ports _ _ _ _ _
    patchRegisters_injective patchStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    have h2 : i ≠ 2 := fun h => hi ⟨2, h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨3, h.symm⟩
    have h8 : i ≠ 8 := fun h => hi ⟨8, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨9, h.symm⟩
    change tapes array replacement index ell label valid scope labels width [] [] [] [] aggregate i =
      tapes [] [] [] [] [] [] scope labels width [] [] [] [] aggregate i
    simp only [tapes_eq, h0, h1, h2, h3, h8, h9, ite_false]

theorem patch_eval (earlier : List (List Bool))
    (old low high rest index ell scope labels width : List Bool) (valid : Bool)
    (hi : index.length = earlier.length) (hrows : ∀ row ∈ earlier, row.length = ell.length)
    (hold : old.length = ell.length) (hlow : low.length = ell.length) :
    StructuredCalls.Eval patch
      (SubexpCandidateMaterializer.workCost index.length ell.length high.length + 1)
      (data false true (earlier.flatten ++ (old ++ rest)) [] index ell (low ++ high) [] scope labels
        width [] [] [] [] [valid])
      (data false true (earlier.flatten ++ (low ++ rest)) low [] ell [] [allZero high] scope labels
        width [] [] [] [] [valid]) := by
  have h := SubexpCandidateMaterializer.lifted_eval patchRegisters patchStacks
    patchRegisters_injective patchStacks_injective
    (data false true [] [] [] [] [] [] scope labels width [] [] [] [] [valid])
    earlier old low high rest index ell hi hrows hold hlow
  simpa only [patch, SubexpCandidateMaterializer.inputState,
    SubexpCandidateMaterializer.outputState, embed_patch] using h

private def straight {r s : ℕ} : List (StructuredProgram.Atom r s) → StructuredProgram.Cmd r s
  | [] => .skip
  | a :: as => .seq (.atom a) (straight as)

private def straightResult {r s : ℕ} : List (StructuredProgram.Atom r s) →
    StructuredProgram.State r s → StructuredProgram.State r s
  | [], d => d
  | a :: as, d => straightResult as (a.eval d)

private theorem straight_eval {r s : ℕ} (as : List (StructuredProgram.Atom r s))
    (d : StructuredProgram.State r s) :
    StructuredProgram.Eval (straight as) as.length d (straightResult as d) := by
  induction as generalizing d with
  | nil => exact .skip d
  | cons a as ih =>
      simpa only [straight, straightResult, List.length_cons, Nat.add_comm 1] using
        StructuredProgram.Eval.seq (.atom a d) (ih (a.eval d))

private def combineOps : List (StructuredProgram.Atom 6 18) :=
  [.pop 17 0 2, .pop 9 1 2, .band 0 0 1, .push 17 0,
    .set 0 false, .set 1 false, .set 2 false]

abbrev combineValidity : StructuredCalls.Cmd 6 18 := .base (straight combineOps)

theorem combineValidity_eval (array low ell scope labels width : List Bool)
    (prior current : Bool) :
    StructuredCalls.Eval combineValidity 7
      (data false true array low [] ell [] [current] scope labels width [] [] [] [] [prior])
      (data false true array low [] ell [] [] scope labels width [] [] [] [] [prior && current]) := by
  have h := straight_eval combineOps
    (data false true array low [] ell [] [current] scope labels width [] [] [] [] [prior])
  have heq : straightResult combineOps
      (data false true array low [] ell [] [current] scope labels width [] [] [] [] [prior]) =
      data false true array low [] ell [] [] scope labels width [] [] [] [] [prior && current] := by
    apply state_ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [heq] at h
  exact .base (by simpa only [combineOps, List.length_cons, List.length_nil] using h)

abbrev clearReplacement : StructuredCalls.Cmd 6 18 := .call (clearProgram 1 0 1)

theorem clearReplacement_eval (array low ell scope labels width : List Bool) (valid : Bool) :
    StructuredCalls.Eval clearReplacement (2 * low.length + 3)
      (data false true array low [] ell [] [] scope labels width [] [] [] [] [valid])
      (resting false true array ell scope labels width valid) := by
  have hstore : clearStacks (1 : Fin 18)
      (tapes array low [] ell [] [] scope labels width [] [] [] [] [valid]) =
      tapes array [] [] ell [] [] scope labels width [] [] [] [] [valid] := by
    funext i; fin_cases i <;> simp [clearStacks, tapes]
  have h := ListRegisterProgram.clear_run (1 : Fin 18) (0 : Fin 6) 1 (registers false true)
    (tapes array low [] ell [] [] scope labels width [] [] [] [] [valid])
  rw [hstore] at h
  have hlow : (tapes array low [] ell [] [] scope labels width [] [] [] [] [valid]) 1 =
      low := by simp [tapes]
  rw [read_reset] at h
  apply StructuredCalls.Eval.call
  simpa only [hlow, clearReplacement, data, resting, State.withPC] using h

abbrev callback : StructuredCalls.Cmd 6 18 :=
  .seq decodeIndex (.seq extractRecord (.seq patch (.seq combineValidity clearReplacement)))

def callbackCost (index chunkWidth recordWidth highWidth : ℕ) : ℕ :=
  index * (14 * chunkWidth + 13) + 36 * chunkWidth + 14 * recordWidth + 4 * highWidth + 66

theorem callback_eval (earlier : List (List Bool))
    (old low high rest ell scope labels width : List Bool) (valid : Bool)
    (hrows : ∀ row ∈ earlier, row.length = ell.length)
    (hold : old.length = ell.length) (hlow : low.length = ell.length)
    (hwidth : (low ++ high).length = width.length) :
    StructuredCalls.Eval callback
      (callbackCost earlier.length ell.length width.length high.length)
      (data false true (earlier.flatten ++ (old ++ rest)) [] [] ell [] [] scope
        ((low ++ high) ++ labels) width [] [] [] (Encoding.encodeNat earlier.length).reverse [valid])
      (resting false true (earlier.flatten ++ (low ++ rest)) ell scope labels width
        (valid && allZero high)) := by
  have hd := decodeIndex_eval earlier.length (earlier.flatten ++ (old ++ rest)) ell scope
    ((low ++ high) ++ labels) width valid
  have he := extractRecord_eval (earlier.flatten ++ (old ++ rest))
    (List.replicate earlier.length true) ell scope (low ++ high) labels width valid hwidth
  have hp := patch_eval earlier old low high rest (List.replicate earlier.length true) ell
    scope labels width valid (by simp) hrows hold hlow
  have hc := combineValidity_eval (earlier.flatten ++ (low ++ rest)) low ell scope labels width
    valid (allZero high)
  have hx := clearReplacement_eval (earlier.flatten ++ (low ++ rest)) low ell scope labels width
    (valid && allZero high)
  have h := hd.seq (he.seq (hp.seq (hc.seq hx)))
  convert h using 1
  simp only [callbackCost, SubexpCandidateMaterializer.workCost, List.length_replicate, hlow]
  ring

/-- Concrete list update used only to specify the array written by the machine. -/
def patchChunks : ℕ → List Bool → List (List Bool) → List (List Bool)
  | _, _, [] => []
  | 0, replacement, _ :: rest => replacement :: rest
  | j + 1, replacement, row :: rest => row :: patchChunks j replacement rest

theorem patchChunks_length (j : ℕ) (replacement : List Bool) (chunks : List (List Bool)) :
    (patchChunks j replacement chunks).length = chunks.length := by
  induction chunks generalizing j with
  | nil => simp [patchChunks]
  | cons row rest ih => cases j <;> simp [patchChunks, ih]

theorem patchChunks_append (earlier : List (List Bool)) (old replacement : List Bool)
    (rest : List (List Bool)) :
    patchChunks earlier.length replacement (earlier ++ old :: rest) =
      earlier ++ replacement :: rest := by
  induction earlier with
  | nil => rfl
  | cons row earlier ih => simp [patchChunks, ih]

theorem patchChunks_uniform (j : ℕ) (replacement : List Bool) (chunks : List (List Bool))
    (ell : ℕ) (hnew : replacement.length = ell)
    (hrows : ∀ row ∈ chunks, row.length = ell) :
    ∀ row ∈ patchChunks j replacement chunks, row.length = ell := by
  induction chunks generalizing j with
  | nil => simp [patchChunks]
  | cons row rest ih =>
      cases j with
      | zero => simpa [patchChunks] using And.intro hnew (fun x hx => hrows x (by simp [hx]))
      | succ j =>
          have ht := ih j (fun x hx => hrows x (by simp [hx]))
          simpa [patchChunks] using And.intro (hrows row (by simp)) ht

theorem chunks_split (chunks : List (List Bool)) (j : ℕ) (hj : j < chunks.length) :
    ∃ earlier old rest, chunks = earlier ++ old :: rest ∧ earlier.length = j := by
  induction chunks generalizing j with
  | nil => simp at hj
  | cons row chunks ih =>
      cases j with
      | zero => exact ⟨[], row, chunks, rfl, rfl⟩
      | succ j =>
          obtain ⟨earlier, old, rest, h, hl⟩ := ih j (by simpa using hj)
          exact ⟨row :: earlier, old, rest, by simp [h], by simp [hl]⟩

def materialize {D : ℕ} (ell : ℕ) :
    List (Fin D × List Bool) → List (List Bool) → Bool → List (List Bool) × Bool
  | [], chunks, valid => (chunks, valid)
  | (j, label) :: rest, chunks, valid =>
      materialize ell rest (patchChunks j.val (label.take ell) chunks)
        (valid && allZero (label.drop ell))

def recordPorts : RecordPrograms.Ports 6 18 where
  tag := 3
  present := 4
  found := 5
  source := 10
  payload := 16
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

private theorem record_state (tag present : Bool) (array ell labels width scope payload : List Bool)
    (valid : Bool) :
    RecordPrograms.state recordPorts (resting false false array ell [] labels width valid)
      tag present false scope payload =
      data tag present array [] [] ell [] [] scope labels width [] [] [] payload [valid] := by
  apply state_ext
  · funext i; fin_cases i <;>
      simp [RecordPrograms.state, recordPorts, resting, data, registers]
  · funext i; fin_cases i <;>
      simp [RecordPrograms.state, recordPorts, resting, data, tapes]

theorem read_index (j : ℕ) (array ell scope labels width : List Bool) (valid tag present : Bool) :
    StructuredCalls.Eval (RecordPrograms.reader recordPorts) (6 * (j + 1) + 4)
      (resting tag present array ell (Encoding.frame (Encoding.encodeNat j) ++ scope)
        labels width valid)
      (data false true array [] [] ell [] [] scope labels width [] [] []
        (Encoding.encodeNat j).reverse [valid]) := by
  have h := RecordPrograms.reader_eval recordPorts
    (resting false false array ell [] labels width valid) (Encoding.encodeNat j) scope []
    tag present false
  have hs := record_state tag present array ell labels width
    (Encoding.frame (Encoding.encodeNat j) ++ scope) [] valid
  have hf := record_state false true array ell labels width scope
    (Encoding.encodeNat j).reverse valid
  rw [hs] at h
  simp only [List.append_nil] at h
  rw [hf] at h
  simpa [resting, Encoding.length_encodeNat, List.append_nil] using h

abbrev popScope : StructuredCalls.Cmd 6 18 := .base (.atom (.pop 10 3 4))

theorem pop_scope (array ell scope labels width : List Bool) (valid tag present bit : Bool) :
    StructuredCalls.Eval popScope 1
      (resting tag present array ell (bit :: scope) labels width valid)
      (resting bit true array ell scope labels width valid) := by
  have h := StructuredProgram.Eval.atom (.pop (10 : Fin 18) (3 : Fin 6) 4)
    (resting tag present array ell (bit :: scope) labels width valid)
  have heq : (StructuredProgram.Atom.pop (10 : Fin 18) (3 : Fin 6) 4).eval
      (resting tag present array ell (bit :: scope) labels width valid) =
      resting bit true array ell scope labels width valid := by
    apply state_ext
    · funext i; fin_cases i <;> simp [resting, data, registers, tapes,
        Atom.eval, Atom.instr, State.ofCfg, execInstr, readRegs]
    · funext i; fin_cases i <;> simp [resting, data, tapes,
        Atom.eval, Atom.instr, State.ofCfg, execInstr]
  exact .base (heq ▸ h)

def scopeBytes {D : ℕ} (jobs : List (Fin D × List Bool)) : List Bool :=
  Encoding.encodeList Encoding.encodeNat (jobs.map fun job => job.1.val)

def labelBytes {D : ℕ} (jobs : List (Fin D × List Bool)) : List Bool :=
  (jobs.map Prod.snd).flatten

def afterTag {D : ℕ} (chunks : List (List Bool)) (ell width : List Bool)
    (jobs : List (Fin D × List Bool)) (scopeSuffix labelSuffix : List Bool) (valid : Bool) : Data :=
  match jobs with
  | [] => resting false true chunks.flatten ell scopeSuffix labelSuffix width valid
  | (j, label) :: rest => resting true true chunks.flatten ell
      (Encoding.frame (Encoding.encodeNat j.val) ++ (scopeBytes rest ++ scopeSuffix))
      (label ++ (labelBytes rest ++ labelSuffix)) width valid

theorem pop_tag {D : ℕ} (chunks : List (List Bool)) (ell width : List Bool)
    (jobs : List (Fin D × List Bool)) (scopeSuffix labelSuffix : List Bool)
    (valid tag present : Bool) :
    StructuredCalls.Eval popScope 1
      (resting tag present chunks.flatten ell (scopeBytes jobs ++ scopeSuffix)
        (labelBytes jobs ++ labelSuffix) width valid)
      (afterTag chunks ell width jobs scopeSuffix labelSuffix valid) := by
  cases jobs with
  | nil => simpa [afterTag, scopeBytes, labelBytes, Encoding.encodeList] using
      pop_scope chunks.flatten ell scopeSuffix labelSuffix width valid tag present false
  | cons job rest =>
      rcases job with ⟨j, label⟩
      simpa [afterTag, scopeBytes, labelBytes, Encoding.encodeList, List.append_assoc] using
        pop_scope chunks.flatten ell
          (Encoding.frame (Encoding.encodeNat j.val) ++ (scopeBytes rest ++ scopeSuffix))
          (label ++ (labelBytes rest ++ labelSuffix)) width valid tag present true

abbrev rowCommand : StructuredCalls.Cmd 6 18 := .seq (RecordPrograms.reader recordPorts) callback

abbrev rowLoop : StructuredCalls.Cmd 6 18 := .while 3 (.seq rowCommand popScope)

def rowCost {D : ℕ} (ell width : ℕ) : List (Fin D × List Bool) → ℕ
  | [] => 0
  | (j, label) :: rest =>
      callbackCost j.val ell width (label.drop ell).length + 6 * (j.val + 1) + 6 + rowCost ell width rest

theorem row_eval {D : ℕ} (chunks : List (List Bool)) (ell width : List Bool)
    (j : Fin D) (label scope labels : List Bool) (valid : Bool)
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell.length)
    (hwidth : label.length = width.length) (hell : ell.length ≤ width.length) :
    StructuredCalls.Eval rowCommand
      ((6 * (j.val + 1) + 4) + callbackCost j.val ell.length width.length (label.drop ell.length).length)
      (resting true true chunks.flatten ell (Encoding.frame (Encoding.encodeNat j.val) ++ scope)
        (label ++ labels) width valid)
      (resting false true (patchChunks j.val (label.take ell.length) chunks).flatten ell scope labels
        width (valid && allZero (label.drop ell.length))) := by
  obtain ⟨earlier, old, rest, hsplit, hlen⟩ := chunks_split chunks j.val (by simp [hcount])
  have hearly : ∀ row ∈ earlier, row.length = ell.length := by
    intro row hr
    exact hrows row (by rw [hsplit]; simp [hr])
  have hold : old.length = ell.length := hrows old (by rw [hsplit]; simp)
  have hlow : (label.take ell.length).length = ell.length := by
    simp [List.length_take, hwidth, Nat.min_eq_left hell]
  have hflat : chunks.flatten = earlier.flatten ++ (old ++ rest.flatten) := by
    rw [hsplit]
    simp [List.flatten_append, List.flatten_cons ]
  have hnew : (patchChunks j.val (label.take ell.length) chunks).flatten =
      earlier.flatten ++ (label.take ell.length ++ rest.flatten) := by
    rw [hsplit, ← hlen, patchChunks_append]
    simp [List.flatten_append, List.flatten_cons ]
  have hr := read_index j.val chunks.flatten ell scope (label ++ labels) width valid true true
  have hc := callback_eval earlier old (label.take ell.length) (label.drop ell.length) rest.flatten
    ell scope labels width valid hearly hold hlow (by simpa using hwidth)
  rw [hlen, ← hflat, ← hnew, List.take_append_drop] at hc
  exact hr.seq hc

theorem row_loop_eval {D : ℕ} (jobs : List (Fin D × List Bool)) (chunks : List (List Bool))
    (ell width scopeSuffix labelSuffix : List Bool) (valid : Bool)
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell.length)
    (hwidth : ∀ job ∈ jobs, job.2.length = width.length) (hell : ell.length ≤ width.length) :
    StructuredCalls.Eval rowLoop (rowCost ell.length width.length jobs + 1)
      (afterTag chunks ell width jobs scopeSuffix labelSuffix valid)
      (resting false true (materialize ell.length jobs chunks valid).1.flatten ell scopeSuffix
        labelSuffix width (materialize ell.length jobs chunks valid).2) := by
  induction jobs generalizing chunks valid with
  | nil =>
      exact .while_false rfl
  | cons job rest ih =>
      rcases job with ⟨j, label⟩
      have hw := hwidth (j, label) (by simp)
      have hlow : (label.take ell.length).length = ell.length := by
        simp [List.length_take, hw, Nat.min_eq_left hell]
      have hn : (patchChunks j.val (label.take ell.length) chunks).length = D := by
        rw [patchChunks_length, hcount]
      have hr := patchChunks_uniform j.val (label.take ell.length) chunks ell.length hlow hrows
      have h₁ := row_eval chunks ell width j label (scopeBytes rest ++ scopeSuffix)
        (labelBytes rest ++ labelSuffix) valid hcount hrows hw hell
      have h₂ := pop_tag (patchChunks j.val (label.take ell.length) chunks) ell width rest scopeSuffix
        labelSuffix (valid && allZero (label.drop ell.length)) false true
      have h₃ := ih (patchChunks j.val (label.take ell.length) chunks)
        (valid && allZero (label.drop ell.length)) hn hr
        (fun job hj => hwidth job (by simp [hj]))
      have h := StructuredCalls.Eval.while_true (test := (3 : Fin 6)) rfl (h₁.seq h₂) h₃
      convert h using 1
      · simp only [rowCost]
        omega
      · rfl
      · rw [materialize.eq_def]

abbrev command : StructuredCalls.Cmd 6 18 := .seq popScope rowLoop

def program := StructuredCalls.compiled command (10 : Fin 18) 0

theorem command_size : StructuredCalls.size command = 114 := rfl

theorem command_eval {D : ℕ} (jobs : List (Fin D × List Bool)) (chunks : List (List Bool))
    (ell width scopeSuffix labelSuffix : List Bool) (valid : Bool)
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell.length)
    (hwidth : ∀ job ∈ jobs, job.2.length = width.length) (hell : ell.length ≤ width.length) :
    StructuredCalls.Eval command (rowCost ell.length width.length jobs + 2)
      (resting false false chunks.flatten ell (scopeBytes jobs ++ scopeSuffix)
        (labelBytes jobs ++ labelSuffix) width valid)
      (resting false true (materialize ell.length jobs chunks valid).1.flatten ell scopeSuffix
        labelSuffix width (materialize ell.length jobs chunks valid).2) := by
  have h := (pop_tag chunks ell width jobs scopeSuffix labelSuffix valid false false).seq
    (row_loop_eval jobs chunks ell width scopeSuffix labelSuffix valid hcount hrows hwidth hell)
  convert h using 1
  omega

theorem trace {D : ℕ} (jobs : List (Fin D × List Bool)) (chunks : List (List Bool))
    (ell width scopeSuffix labelSuffix : List Bool) (valid : Bool)
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell.length)
    (hwidth : ∀ job ∈ jobs, job.2.length = width.length) (hell : ell.length ≤ width.length) :
    Trace program (rowCost ell.length width.length jobs + 3)
      ((resting false false chunks.flatten ell (scopeBytes jobs ++ scopeSuffix)
        (labelBytes jobs ++ labelSuffix) width valid).withPC (some program.entry))
      ((resting false true (materialize ell.length jobs chunks valid).1.flatten ell scopeSuffix
        labelSuffix width (materialize ell.length jobs chunks valid).2).withPC none) := by
  simpa only [program, Nat.add_assoc] using StructuredCalls.compiled_halt_trace
    (command_eval jobs chunks ell width scopeSuffix labelSuffix valid hcount hrows hwidth hell) 10 0

theorem materialize_validity {D : ℕ} (ell : ℕ) (jobs : List (Fin D × List Bool))
    (chunks : List (List Bool)) (valid : Bool) :
    (materialize ell jobs chunks valid).2 =
      (valid && jobs.all (fun job => allZero (job.2.drop ell))) := by
  induction jobs generalizing chunks valid with
  | nil => simp [materialize]
  | cons job rest ih => rcases job with ⟨j, label⟩; simp [materialize, ih, Bool.and_assoc]

theorem materialize_validity_iff {D : ℕ} (ell : ℕ) (jobs : List (Fin D × List Bool))
    (chunks : List (List Bool)) (valid : Bool)
    (hwidth : ∀ job ∈ jobs, ell ≤ job.2.length) :
    (materialize ell jobs chunks valid).2 = true ↔
      valid = true ∧ ∀ job ∈ jobs, BinaryArithmetic.toNat job.2 < 2 ^ ell := by
  simp only [materialize_validity, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨hv, hall⟩
    refine ⟨hv, ?_⟩
    intro job hj
    have h := (unary_validity_iff (job.2.take ell) (job.2.drop ell)).mp (hall job hj)
    simpa only [List.take_append_drop, List.length_take, Nat.min_eq_left (hwidth job hj)] using h
  · rintro ⟨hv, hall⟩
    refine ⟨hv, ?_⟩
    intro job hj
    apply (unary_validity_iff (job.2.take ell) (job.2.drop ell)).mpr
    simpa only [List.take_append_drop, List.length_take, Nat.min_eq_left (hwidth job hj)] using hall job hj

theorem materialize_length {D : ℕ} (ell : ℕ) (jobs : List (Fin D × List Bool))
    (chunks : List (List Bool)) (valid : Bool) :
    (materialize ell jobs chunks valid).1.length = chunks.length := by
  induction jobs generalizing chunks valid with
  | nil => rfl
  | cons job rest ih =>
      rcases job with ⟨j, label⟩
      simp only [materialize, ih, patchChunks_length]

theorem materialize_uniform {D : ℕ} (ell width : ℕ) (jobs : List (Fin D × List Bool))
    (chunks : List (List Bool)) (valid : Bool)
    (hrows : ∀ row ∈ chunks, row.length = ell)
    (hwidth : ∀ job ∈ jobs, job.2.length = width) (hell : ell ≤ width) :
    ∀ row ∈ (materialize ell jobs chunks valid).1, row.length = ell := by
  induction jobs generalizing chunks valid with
  | nil => exact hrows
  | cons job rest ih =>
      rcases job with ⟨j, label⟩
      have hl : (label.take ell).length = ell := by
        rw [List.length_take, hwidth (j, label) (by simp), Nat.min_eq_left hell]
      exact ih _ _ (patchChunks_uniform _ _ _ _ hl hrows)
        (fun job hj => hwidth job (by simp [hj]))

theorem flatten_length_uniform (chunks : List (List Bool)) (ell : ℕ)
    (hrows : ∀ row ∈ chunks, row.length = ell) :
    chunks.flatten.length = chunks.length * ell := by
  induction chunks with
  | nil => simp
  | cons row rest ih =>
      have ht := ih (fun x hx => hrows x (by simp [hx]))
      simp only [List.flatten_cons, List.length_append, List.length_cons,
        hrows row (by simp), ht]
      ring

theorem patchChunks_get_self (chunks : List (List Bool)) (j : ℕ) (replacement : List Bool)
    (hj : j < chunks.length) : (patchChunks j replacement chunks)[j]? = some replacement := by
  induction chunks generalizing j with
  | nil => simp at hj
  | cons row rest ih =>
      cases j with
      | zero => rfl
      | succ j =>
          simpa [patchChunks] using ih j (by simpa using hj)

theorem patchChunks_get_other (chunks : List (List Bool)) (j i : ℕ) (replacement : List Bool)
    (hne : i ≠ j) : (patchChunks j replacement chunks)[i]? = chunks[i]? := by
  induction chunks generalizing j i with
  | nil => simp [patchChunks]
  | cons row rest ih =>
      cases j <;> cases i <;> simp_all [patchChunks]

theorem materialize_not_mem {D : ℕ} (ell : ℕ) (jobs : List (Fin D × List Bool))
    (chunks : List (List Bool)) (valid : Bool) (j : Fin D)
    (hj : j ∉ jobs.map Prod.fst) :
    (materialize ell jobs chunks valid).1[j.val]? = chunks[j.val]? := by
  induction jobs generalizing chunks valid with
  | nil => rfl
  | cons job rest ih =>
      rcases job with ⟨k, label⟩
      have htail : j ∉ rest.map Prod.fst := by
        intro h
        exact hj (by simp [h])
      have hne : j.val ≠ k.val := by
        intro h
        have he : j = k := Fin.ext h
        exact hj (by simp [he])
      simp only [materialize]
      rw [ih _ _ htail, patchChunks_get_other chunks k.val j.val _ hne]

/-- With distinct scope indices, each supplied local label occupies its own
chunk in the final stored array, in exactly the emitted scope order. -/
theorem materialize_lookup {D : ℕ} (ell : ℕ) (jobs : List (Fin D × List Bool))
    (chunks : List (List Bool)) (valid : Bool) (j : Fin D) (label : List Bool)
    (hcount : chunks.length = D) (hdistinct : (jobs.map Prod.fst).Nodup)
    (hmem : (j, label) ∈ jobs) :
    (materialize ell jobs chunks valid).1[j.val]? = some (label.take ell) := by
  induction jobs generalizing chunks valid with
  | nil => simp at hmem
  | cons job rest ih =>
      rcases job with ⟨k, headLabel⟩
      have hnd : k ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by
        simpa using hdistinct
      rcases List.mem_cons.mp hmem with heq | htail
      · obtain ⟨hjk, hlabel⟩ := Prod.mk.inj heq
        subst k
        subst headLabel
        simp only [materialize]
        rw [materialize_not_mem ell rest _ _ j hnd.1]
        exact patchChunks_get_self chunks j.val (label.take ell) (by simp [hcount])
      · exact ih (patchChunks k.val (headLabel.take ell) chunks)
          (valid && allZero (headLabel.drop ell))
          (by rw [patchChunks_length, hcount]) hnd.2 htail

theorem rowCost_le {D : ℕ} (ell width : ℕ) (jobs : List (Fin D × List Bool))
    (hwidth : ∀ job ∈ jobs, job.2.length = width) :
    rowCost ell width jobs ≤
      jobs.length * (D * (14 * ell + 19) + 36 * ell + 18 * width + 78) := by
  induction jobs with
  | nil => simp [rowCost]
  | cons job rest ih =>
      rcases job with ⟨j, label⟩
      have ht := ih (fun x hx => hwidth x (by simp [hx]))
      have hl : (label.drop ell).length ≤ width := by
        rw [List.length_drop, hwidth (j, label) (by simp)]
        exact Nat.sub_le _ _
      have hm := Nat.mul_le_mul_right (14 * ell + 19) (Nat.le_of_lt j.isLt)
      simp only [rowCost, callbackCost, List.length_cons]
      nlinarith

theorem run_bounded {D : ℕ} (jobs : List (Fin D × List Bool)) (chunks : List (List Bool))
    (ell width scopeSuffix labelSuffix : List Bool) (valid : Bool)
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell.length)
    (hwidth : ∀ job ∈ jobs, job.2.length = width.length) (hell : ell.length ≤ width.length) :
    BitProgram.RunsIn program
      (jobs.length * (D * (14 * ell.length + 19) + 36 * ell.length + 18 * width.length + 78) + 3)
      ((resting false false chunks.flatten ell (scopeBytes jobs ++ scopeSuffix)
        (labelBytes jobs ++ labelSuffix) width valid).withPC (some program.entry))
      ((resting false true (materialize ell.length jobs chunks valid).1.flatten ell scopeSuffix
        labelSuffix width (materialize ell.length jobs chunks valid).2).withPC none) :=
  ⟨_, Nat.add_le_add_right (rowCost_le ell.length width.length jobs hwidth) 3,
    trace jobs chunks ell width scopeSuffix labelSuffix valid hcount hrows hwidth hell⟩

theorem lifted_eval {R S D : ℕ} (register : Fin 6 → Fin R) (stack : Fin 18 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (frame : StructuredProgram.State R S) (jobs : List (Fin D × List Bool))
    (chunks : List (List Bool)) (ell width scopeSuffix labelSuffix : List Bool) (valid : Bool)
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell.length)
    (hwidth : ∀ job ∈ jobs, job.2.length = width.length) (hell : ell.length ≤ width.length) :
    StructuredCalls.Eval (.call (ProgramLinking.liftProgram program register stack))
      (rowCost ell.length width.length jobs + 3)
      (StructuredCalls.embedState register stack frame
        (resting false false chunks.flatten ell (scopeBytes jobs ++ scopeSuffix)
          (labelBytes jobs ++ labelSuffix) width valid))
      (StructuredCalls.embedState register stack frame
        (resting false true (materialize ell.length jobs chunks valid).1.flatten ell scopeSuffix
          labelSuffix width (materialize ell.length jobs chunks valid).2)) :=
  StructuredCalls.eval_call_lifted program register stack frame hregister hstack
    (trace jobs chunks ell width scopeSuffix labelSuffix valid hcount hrows hwidth hell)

theorem primitive_execution {D : ℕ} (jobs : List (Fin D × List Bool)) (chunks : List (List Bool))
    (ell width scopeSuffix labelSuffix : List Bool) (valid : Bool)
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell.length)
    (hwidth : ∀ job ∈ jobs, job.2.length = width.length) (hell : ell.length ≤ width.length) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (rowCost ell.length width.length jobs + 3))
      (BitProgram.primitiveCfg program
        ((resting false false chunks.flatten ell (scopeBytes jobs ++ scopeSuffix)
          (labelBytes jobs ++ labelSuffix) width valid).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((resting false true (materialize ell.length jobs chunks valid).1.flatten ell scopeSuffix
          labelSuffix width (materialize ell.length jobs chunks valid).2).withPC none)) :=
  BitProgram.primitive_trace program
    (trace jobs chunks ell width scopeSuffix labelSuffix valid hcount hrows hwidth hell)

end SubexponentialSAT.SubexpScopeMaterializer

end OAI.Algorithms
