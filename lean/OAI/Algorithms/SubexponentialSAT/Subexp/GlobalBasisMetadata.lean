import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorOutput
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

namespace OAI.Algorithms

/-!
# Physical packing metadata lookup

The raw packing table and query remain on stacks 0 and 1. A successful lookup
returns either a block/type pair on 2/3, or a leftover rank on 4. Register 4
distinguishes those cases; all other registers and stacks 5 through 11 are
cleared. Keys, indices, and type encodings are runtime words.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisMetadata

open BitProgram StructuredCalls SubexpScanPrimitives


abbrev Data := State 5 12
abbrev Code := Cmd 5 12
abbrev Regs := Fin 5 → Bool

inductive Metadata where
  | covered (block typeCode : List Bool)
  | leftover (rank : List Bool)

def Metadata.encode : Metadata → List Bool
  | .covered block typeCode => true :: (Encoding.frame block ++ Encoding.frame typeCode)
  | .leftover rank => false :: Encoding.frame rank

def Metadata.coveredFlag : Metadata → Bool
  | .covered .. => true
  | .leftover .. => false

def Metadata.block : Metadata → List Bool
  | .covered block _ => block
  | .leftover _ => []

def Metadata.typeCode : Metadata → List Bool
  | .covered _ typeCode => typeCode
  | .leftover _ => []

def Metadata.rank : Metadata → List Bool
  | .covered .. => []
  | .leftover rank => rank

def work (regs : Regs) (master query source payload saved : List Bool) : Data :=
  ⟨regs, ![master, query, [], [], [], source, payload, saved, [], [], [], []]⟩

def inputState (regs : Regs) (master query : List Bool) : Data :=
  work regs master query [] [] []

def outputState (master query : List Bool) (m : Metadata) : Data :=
  ⟨![false, false, false, false, m.coveredFlag],
    ![master, query, m.block, m.typeCode, m.rank, [], [], [], [], [], [], []]⟩

def reset (regs : Regs) : Regs := readRegs regs 0 1 none

@[simp] theorem reset_reset (regs : Regs) : reset (reset regs) = reset regs :=
  StackRoutines.readRegs_reset regs 0 1 none

def copy (src dst : Fin 12) : Code := .call (StackRoutines.copyProgram src dst 11 0 1)
def transfer (src dst : Fin 12) : Code := .call (StackRoutines.transferProgram src dst 0 1)
def clear (src : Fin 12) : Code := .call (StackRoutines.clearProgram src 0 1)

def cleared (src : Fin 12) (d : Data) : Data :=
  ⟨reset d.regs, Function.update d.stacks src []⟩

theorem clear_eval (src : Fin 12) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) := by
  exact .call _ (ListRegisterProgram.clear_run src (0 : Fin 5) 1 d.regs d.stacks)

def load : Code := .seq (copy 0 5) (.seq (copy 1 6) (transfer 6 7))

theorem load_eval (regs : Regs) (master query : List Bool) :
    Eval load (7 * master.length + 10 * query.length + 13)
      (inputState regs master query)
      (work (reset regs) master query master [] query.reverse) := by
  let a := inputState regs master query
  let b := afterCopy a 0 5 0 1
  let c := afterCopy b 1 6 0 1
  let d := afterTransfer c 6 7 0 1
  have h1 := SubexpScanPrimitives.copy_eval a 0 5 11 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have h2 := SubexpScanPrimitives.copy_eval b 1 6 11 0 1
    (by decide) (by decide) (by decide) (by decide) (by rfl)
  have h3 := SubexpScanPrimitives.transfer_eval c 6 7 0 1 (by decide) (by decide)
  have he : d = work (reset regs) master query master [] query.reverse := by
    apply state_ext
    · simp [d, c, b, a, afterTransfer, afterCopy, inputState, work, reset,
        StackRoutines.readRegs_reset]
    · funext i
      fin_cases i <;> simp [d, c, b, a, afterTransfer, afterCopy, inputState,
        work, StackRoutines.copyStacks, StackRoutines.transferStacks]
  have h := h1.seq (h2.seq h3)
  change Eval load _ a d at h
  rw [he] at h
  convert h using 1
  simp [a, b, c, inputState, work, afterCopy, StackRoutines.copyStacks]
  omega

def selectorPort (i : Fin 6) : Fin 12 := ⟨5 + i.val, by omega⟩

theorem selectorPort_injective : Function.Injective selectorPort := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 5 + i.val = 5 + j.val at hv
  omega

def selector : Code :=
  .call (ProgramLinking.liftProgram SelectorProgram.program id selectorPort)

theorem selector_eval (records : List (List Bool × List Bool)) (query : List Bool)
    (regs : Regs) (master : List Bool) :
    ∃ n ≤ SelectorProgram.budget query records, ∃ rf tail,
      tail.length ≤ (SelectorProgram.rawRecords records).length + query.length + n ∧
      Eval selector n
        (work regs master query (SelectorProgram.rawRecords records) [] query.reverse)
        (work rf master query tail ((records.lookup query).getD query).reverse query.reverse) := by
  obtain ⟨n, hn, rf, tail, ht⟩ := SelectorProgram.program_trace query records regs
  have hspace := trace_dataBits SelectorProgram.program ht
  have htail : tail.length ≤ (SelectorProgram.rawRecords records).length + query.length + n := by
    simp [dataBits, stackBits,
      Fin.sum_univ_succ] at hspace
    omega
  let a := work regs master query (SelectorProgram.rawRecords records) [] query.reverse
  let b := work rf master query tail ((records.lookup query).getD query).reverse query.reverse
  have ha : embedState id selectorPort a
      (SubexpRecordScan.recordState regs (SelectorProgram.rawRecords records) [] query.reverse [] [] []) = a := by
    apply embedState_eq id selectorPort Function.injective_id selectorPort_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact (hj ⟨j, rfl⟩).elim
    · intro j hj; rfl
  have hb : embedState id selectorPort a
      (SubexpRecordScan.recordState rf tail ((records.lookup query).getD query).reverse query.reverse [] [] []) = b := by
    apply embedState_eq id selectorPort Function.injective_id selectorPort_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact (hj ⟨j, rfl⟩).elim
    · intro j hj
      fin_cases j <;> simp_all [a, b, work, selectorPort, Fin.exists_fin_succ]
  have he := eval_call_lifted SelectorProgram.program id selectorPort a
    Function.injective_id selectorPort_injective ht
  exact ⟨n, hn, rf, tail, htail, by simpa only [selector, ha, hb] using he⟩

def cleanup : Code := .seq (clear 5) (.seq (clear 7) (transfer 6 5))

theorem cleanup_eval (regs : Regs) (master query tail payload : List Bool) :
    Eval cleanup (2 * tail.length + 2 * query.length + 3 * payload.length + 9)
      (work regs master query tail payload.reverse query.reverse)
      (work (reset regs) master query payload [] []) := by
  let a := work regs master query tail payload.reverse query.reverse
  let b := cleared 5 a
  let c := cleared 7 b
  let d := afterTransfer c 6 5 0 1
  have h1 := clear_eval 5 a
  have h2 := clear_eval 7 b
  have h3 := SubexpScanPrimitives.transfer_eval c 6 5 0 1 (by decide) (by decide)
  have he : d = work (reset regs) master query payload [] [] := by
    apply state_ext
    · simp [d, c, b, a, cleared, afterTransfer, work, reset, StackRoutines.readRegs_reset]
    · funext i
      fin_cases i <;> simp [d, c, b, a, cleared, afterTransfer, work,
        StackRoutines.transferStacks]
  have h := h1.seq (h2.seq h3)
  change Eval cleanup _ a d at h
  rw [he] at h
  convert h using 1
  simp [a, b, c, cleared, work]
  omega

def parserReg (i : Fin 2) : Fin 5 := Fin.castAdd 3 i
def parserPort (src dst : Fin 12) : Fin 2 → Fin 12 := ![src, dst]

theorem parserReg_injective : Function.Injective parserReg := Fin.castAdd_injective 2 3
theorem parserPort_injective (src dst : Fin 12) (h : src ≠ dst) :
    Function.Injective (parserPort src dst) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [parserPort]

def frame (src dst : Fin 12) : Code :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram parserReg (parserPort src dst))

def framed (d : Data) (src dst : Fin 12) (bits rest : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 (some false),
    Function.update (Function.update d.stacks src rest) dst (bits.reverse ++ d.stacks dst)⟩

theorem frame_eval (d : Data) (src dst : Fin 12) (hsd : src ≠ dst)
    (bits rest : List Bool) (hin : d.stacks src = Encoding.frame bits ++ rest) :
    Eval (frame src dst) (6 * bits.length + 4) d (framed d src dst bits rest) := by
  let a : State 2 2 := ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
    ParserProgram.pair (Encoding.frame bits ++ rest) (d.stacks dst)⟩
  let b : State 2 2 := ⟨ParserProgram.pair false true,
    ParserProgram.pair rest (bits.reverse ++ d.stacks dst)⟩
  have ha : embedState parserReg (parserPort src dst) d a = d := by
    apply embedState_eq _ _ parserReg_injective (parserPort_injective src dst hsd)
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i
      · exact hin
      · rfl
    · intro j hj; rfl
    · intro j hj; rfl
  have hb : embedState parserReg (parserPort src dst) d b = framed d src dst bits rest := by
    apply embedState_eq _ _ parserReg_injective (parserPort_injective src dst hsd)
    · intro i; fin_cases i <;> simp [framed, b, parserReg, ParserProgram.pair, readRegs]
    · intro i; fin_cases i <;> simp [framed, b, parserPort, ParserProgram.pair, hsd]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [parserReg] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [parserReg] using h.symm⟩
      simp [framed, readRegs, h0, h1]
    · intro j hj
      have hs : j ≠ src := fun h => hj ⟨0, by simpa [parserPort] using h.symm⟩
      have hd : j ≠ dst := fun h => hj ⟨1, by simpa [parserPort] using h.symm⟩
      simp [framed, hs, hd]
  have ht : Trace ParserProgram.frameProgram (6 * bits.length + 4)
      (a.withPC (some ParserProgram.frameProgram.entry)) (b.withPC none) :=
    ParserProgram.frame_trace bits rest (d.stacks dst) (d.regs 0) (d.regs 1)
  have he := eval_call_lifted ParserProgram.frameProgram parserReg (parserPort src dst) d
    parserReg_injective (parserPort_injective src dst hsd) ht
  simpa only [frame, ha, hb] using he

def header : Code := .base (.atom (.pop 5 4 0))
def headed (d : Data) : Data :=
  (StructuredProgram.Atom.pop (5 : Fin 12) (4 : Fin 5) 0).eval d
def coveredBody : Code := .seq (frame 5 6)
  (.seq (transfer 6 2) (.seq (frame 5 6) (transfer 6 3)))
def leftoverBody : Code := .seq (frame 5 6) (transfer 6 4)
def finish : Code := RegisterResetProgram.clear [0, 1, 2, 3]
def parse : Code := .seq header (.seq (.ite 4 coveredBody leftoverBody) finish)

def parseCost : Metadata → ℕ
  | .covered block typeCode => 9 * block.length + 9 * typeCode.length + 20
  | .leftover rank => 9 * rank.length + 13

theorem parse_eval (m : Metadata) (regs : Regs) (master query : List Bool) :
    Eval parse (parseCost m) (work regs master query m.encode [] [])
      (outputState master query m) := by
  cases m with
  | covered block typeCode =>
    let a := work regs master query (Metadata.covered block typeCode).encode [] []
    let b := headed a
    let c := framed b 5 6 block (Encoding.frame typeCode)
    let d := afterTransfer c 6 2 0 1
    let e := framed d 5 6 typeCode []
    let f := afterTransfer e 6 3 0 1
    have hh : Eval header 1 a b := .base (.atom _ _)
    have h1 := frame_eval b 5 6 (by decide) block (Encoding.frame typeCode) rfl
    have h2 := SubexpScanPrimitives.transfer_eval c 6 2 0 1 (by decide) (by decide)
    have h3 := frame_eval d 5 6 (by decide) typeCode [] (by simp [d, c, framed,
      afterTransfer, StackRoutines.transferStacks])
    have h4 := SubexpScanPrimitives.transfer_eval e 6 3 0 1 (by decide) (by decide)
    have hf := RegisterResetProgram.clear_eval ([0, 1, 2, 3] : List (Fin 5)) f
    have hfinal : RegisterResetProgram.cleared [0, 1, 2, 3] f =
        outputState master query (.covered block typeCode) := by
      apply state_ext
      · funext i
        fin_cases i <;> simp [RegisterResetProgram.cleared, f, e, d, c, b, a,
          framed, afterTransfer, headed, work, Metadata.encode, outputState,
          Metadata.coveredFlag, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr, readRegs]
      · funext i
        fin_cases i <;> simp [RegisterResetProgram.cleared, f, e, d, c, b, a,
          framed, afterTransfer, headed, work, Metadata.encode, outputState,
          Metadata.block, Metadata.typeCode, Metadata.rank, StackRoutines.transferStacks,
          StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
    rw [hfinal] at hf
    have hbody := h1.seq (h2.seq (h3.seq h4))
    have hbranch : Eval (.ite 4 coveredBody leftoverBody) _ b f := .ite_true (by rfl) hbody
    have h := hh.seq (hbranch.seq hf)
    change Eval parse _ a (outputState master query (.covered block typeCode)) at h
    convert h using 1 ; simp [parseCost, c, d, e, framed, afterTransfer,
      StackRoutines.transferStacks, a, b, headed, work, Metadata.encode,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr] ; omega
  | leftover rank =>
    let a := work regs master query (Metadata.leftover rank).encode [] []
    let b := headed a
    let c := framed b 5 6 rank []
    let d := afterTransfer c 6 4 0 1
    have hh : Eval header 1 a b := .base (.atom _ _)
    have h1 := frame_eval b 5 6 (by decide) rank [] (by simp [b, a, headed, work,
      Metadata.encode, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr])
    have h2 := SubexpScanPrimitives.transfer_eval c 6 4 0 1 (by decide) (by decide)
    have hf := RegisterResetProgram.clear_eval ([0, 1, 2, 3] : List (Fin 5)) d
    have hfinal : RegisterResetProgram.cleared [0, 1, 2, 3] d =
        outputState master query (.leftover rank) := by
      apply state_ext
      · funext i
        fin_cases i <;> simp [RegisterResetProgram.cleared, d, c, b, a,
          framed, afterTransfer, headed, work, Metadata.encode, outputState,
          Metadata.coveredFlag, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr, readRegs]
      · funext i
        fin_cases i <;> simp [RegisterResetProgram.cleared, d, c, b, a,
          framed, afterTransfer, headed, work, Metadata.encode, outputState,
          Metadata.block, Metadata.typeCode, Metadata.rank, StackRoutines.transferStacks,
          StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
    rw [hfinal] at hf
    have hbody := h1.seq h2
    have hbranch : Eval (.ite 4 coveredBody leftoverBody) _ b d := .ite_false (by rfl) hbody
    have h := hh.seq (hbranch.seq hf)
    change Eval parse _ a (outputState master query (.leftover rank)) at h
    convert h using 1 ; simp [parseCost, c, framed, a, b, headed, work, Metadata.encode,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr] ; omega

theorem parseCost_le (m : Metadata) : parseCost m ≤ 10 * m.encode.length + 20 := by
  cases m <;> simp [parseCost, Metadata.encode] <;> omega

theorem payload_length_le (records : List (List Bool × List Bool)) (query payload : List Bool)
    (h : records.lookup query = some payload) :
    payload.length ≤ (SelectorProgram.rawRecords records).length := by
  obtain ⟨before, after, rfl, _⟩ := List.lookup_eq_some_iff.mp h
  simp [SelectorProgram.rawRecords, List.flatMap_append]
  omega

theorem scanBudget_le (records : List (List Bool × List Bool)) (query : List Bool) :
    SelectorProgram.scanBudget query records ≤
      (9 * query.length + 20) * (SelectorProgram.rawRecords records).length + 1 := by
  induction records with
  | nil => simp [SelectorProgram.scanBudget, SelectorProgram.rawRecords]
  | cons item records ih =>
    rcases item with ⟨key, payload⟩
    simp only [SelectorProgram.scanBudget, SelectorProgram.rawRecords,
      List.flatMap_cons, List.length_append, Encoding.length_frame] at *
    unfold SubexpRecordScan.recordCost
    nlinarith

def volume (records : List (List Bool × List Bool)) (query : List Bool) : ℕ :=
  (SelectorProgram.rawRecords records).length + query.length + 1

theorem budget_le (records : List (List Bool × List Bool)) (query payload : List Bool)
    (h : records.lookup query = some payload) :
    SelectorProgram.budget query records ≤ 50 * (volume records query) ^ 2 := by
  have hs := scanBudget_le records query
  have hp := payload_length_le records query payload h
  unfold SelectorProgram.budget
  rw [h]
  simp only [SelectorProgram.materializeBudget]
  unfold volume
  nlinarith

/-- The same physical lookup is reusable for side-index and local-table
payloads. Its result is a forward word on stack 5; no payload interpretation
is performed by this subroutine. -/
def lookupCommand : Code := .seq load (.seq selector cleanup)

theorem lookup_eval (records : List (List Bool × List Bool)) (query payload : List Bool)
    (h : records.lookup query = some payload) (regs : Regs) :
    ∃ n ≤ 200 * (volume records query) ^ 2, ∃ rf,
      Eval lookupCommand n (inputState regs (SelectorProgram.rawRecords records) query)
        (work rf (SelectorProgram.rawRecords records) query payload [] []) := by
  let master := SelectorProgram.rawRecords records
  obtain ⟨n, hn, rf, tail, ht, he⟩ := selector_eval records query (reset regs) master
  rw [h] at he
  have hc := cleanup_eval rf master query tail payload
  have hall := (load_eval regs master query).seq (he.seq hc)
  change Eval lookupCommand _ (inputState regs master query)
    (work (reset rf) master query payload [] []) at hall
  refine ⟨_, ?_, reset rf, hall⟩
  have hb := budget_le records query payload h
  have hm := payload_length_le records query payload h
  have hv : 1 ≤ volume records query := by unfold volume; omega
  have hsq : volume records query ≤ (volume records query) ^ 2 := by
    nlinarith [Nat.mul_le_mul_left (volume records query) hv]
  change 7 * master.length + 10 * query.length + 13 +
    (n + (2 * tail.length + 2 * query.length + 3 * payload.length + 9)) ≤ _
  dsimp only [master]
  have hsmall : (SelectorProgram.rawRecords records).length + query.length + 1 =
      volume records query := rfl
  nlinarith

def lookupProgram := compiled lookupCommand 0 5

theorem lookup_program_runsIn (records : List (List Bool × List Bool)) (query payload : List Bool)
    (h : records.lookup query = some payload) (regs : Regs) :
    ∃ rf, RunsIn lookupProgram (250 * (volume records query) ^ 2)
      ((inputState regs (SelectorProgram.rawRecords records) query).withPC (some lookupProgram.entry))
      ((work rf (SelectorProgram.rawRecords records) query payload [] []).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := lookup_eval records query payload h regs
  refine ⟨rf, n + 1, ?_, compiled_halt_trace he 0 5⟩
  have hv : 0 < volume records query := by unfold volume; omega
  have hp := pow_pos hv 2
  omega

def command : Code := .seq load (.seq selector (.seq cleanup parse))

theorem command_eval (records : List (List Bool × List Bool)) (query : List Bool)
    (m : Metadata) (h : records.lookup query = some m.encode) (regs : Regs) :
    ∃ n ≤ 300 * (volume records query) ^ 2,
      Eval command n (inputState regs (SelectorProgram.rawRecords records) query)
        (outputState (SelectorProgram.rawRecords records) query m) := by
  let master := SelectorProgram.rawRecords records
  obtain ⟨n, hn, rf, tail, ht, he⟩ := selector_eval records query (reset regs) master
  rw [h] at he
  have hp := parse_eval m (reset rf) master query
  have hc := cleanup_eval rf master query tail m.encode
  have hall := (load_eval regs master query).seq (he.seq (hc.seq hp))
  change Eval command _ (inputState regs master query) (outputState master query m) at hall
  refine ⟨_, ?_, hall⟩
  have hb := budget_le records query m.encode h
  have hm := payload_length_le records query m.encode h
  have hparse := parseCost_le m
  have hv : 1 ≤ volume records query := by unfold volume; omega
  have hsq : volume records query ≤ (volume records query) ^ 2 := by
    nlinarith [Nat.mul_le_mul_left (volume records query) hv]
  change 7 * master.length + 10 * query.length + 13 +
    (n + (2 * tail.length + 2 * query.length + 3 * m.encode.length + 9 + parseCost m)) ≤ _
  dsimp [master] at *
  have hsmall : (SelectorProgram.rawRecords records).length + query.length + 1 =
      volume records query := rfl
  nlinarith

def program := compiled command 0 2

theorem program_runsIn (records : List (List Bool × List Bool)) (query : List Bool)
    (m : Metadata) (h : records.lookup query = some m.encode) (regs : Regs) :
    RunsIn program (400 * (volume records query) ^ 2)
      ((inputState regs (SelectorProgram.rawRecords records) query).withPC (some program.entry))
      ((outputState (SelectorProgram.rawRecords records) query m).withPC none) := by
  obtain ⟨n, hn, he⟩ := command_eval records query m h regs
  refine ⟨n + 1, ?_, compiled_halt_trace he 0 2⟩
  have hv : 0 < volume records query := by unfold volume; omega
  have hp := pow_pos hv 2
  omega

end SubexponentialSAT.Subexp.GlobalBasisMetadata

end OAI.Algorithms
