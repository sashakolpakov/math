import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorPairProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-!
# Selecting and framing one factor-coordinate packet

The cache is an ordinary framed list. A runtime unary index controls a loop
that skips exactly that many records, then captures the next record. The
selected coefficients are joined to the incidence's origin/Taylor prefix.
No indexed dictionary, selected coefficient stream, or Ce value is an input.

The cache master on port 7 is preserved. Port 2 contains the unary label;
port 10 contains the reversed incidence prefix; port 11 is an output suffix.
All other ports are initially empty. The output prepends one framed packet
to port 11 and clears the work ports.
-/

namespace SubexponentialSAT.Subexp.LagrangePacketProgram

open BitProgram StructuredCalls

abbrev Word := List Bool
abbrev Data := State 8 12

/-- The incidence data, before a table-row label chooses its basis polynomial. -/
def incidenceFields (origin taylor : Word) : Word :=
  Encoding.frame origin ++ Encoding.frame taylor

/-- Nested form agreed with the beta/Ce consumer. -/
def packet (origin taylor coefficients : Word) : Word :=
  Encoding.frame (incidenceFields origin taylor) ++ Encoding.frame coefficients

@[simp] theorem incidenceFields_length (origin taylor : Word) :
    (incidenceFields origin taylor).length = 2 * origin.length + 2 * taylor.length + 2 := by
  simp [incidenceFields, Encoding.length_frame]
  omega

@[simp] theorem packet_length (origin taylor coefficients : Word) :
    (packet origin taylor coefficients).length =
      4 * origin.length + 4 * taylor.length + 2 * coefficients.length + 6 := by
  simp [packet, Encoding.length_frame]
  omega

def state (regs : Fin 8 → Bool)
    (cursor captured index cache selected saved acc : Word) : Data :=
  ⟨regs, ![cursor, captured, index, [], [], [], [], cache, selected, [], saved, acc]⟩

def smallRegs : Fin 3 → Fin 8 := Fin.castAdd 5
def onlyCursor : Fin 1 → Fin 12 := fun _ => 0

theorem smallRegs_injective : Function.Injective smallRegs := Fin.castAdd_injective _ _
theorem onlyCursor_injective : Function.Injective onlyCursor :=
  fun _ _ _ => Subsingleton.elim _ _

def skippedRegs (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 0 false) 1 true) 2 true

abbrev skipOne : Cmd 8 12 :=
  .call (ProgramLinking.liftProgram ExecCNFRecords.skipProgram smallRegs onlyCursor)

theorem skipOne_eval (regs : Fin 8 → Bool) (bits rest captured index cache selected saved acc : Word) :
    Eval skipOne (5 * bits.length + 8)
      (state regs (true :: (Encoding.frame bits ++ rest)) captured index cache selected saved acc)
      (state (skippedRegs regs) rest captured index cache selected saved acc) := by
  let a := state regs (true :: (Encoding.frame bits ++ rest)) captured index cache selected saved acc
  let b := state (skippedRegs regs) rest captured index cache selected saved acc
  let x : State 3 1 := ⟨ExecCNFRecords.regs (regs 0) (regs 1) (regs 2),
    fun _ => true :: (Encoding.frame bits ++ rest)⟩
  let y : State 3 1 := ⟨ExecCNFRecords.regs false true true, fun _ => rest⟩
  have hx : embedState smallRegs onlyCursor a x = a := by
    apply SelectorMapProgram.embed_eq _ _ smallRegs_injective onlyCursor_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i; rfl
    · intros; rfl
    · intros; rfl
  have hy : embedState smallRegs onlyCursor a y = b := by
    apply SelectorMapProgram.embed_eq _ _ smallRegs_injective onlyCursor_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i; rfl
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨2, h.symm⟩
      simp [b, a, state, skippedRegs, h0, h1, h2]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
      fin_cases j <;> simp_all [b, a, state]
  have ht : Trace ExecCNFRecords.skipProgram (5 * bits.length + 8)
      (x.withPC (some ExecCNFRecords.skipProgram.entry)) (y.withPC none) :=
    ExecCNFRecords.record_trace bits rest (regs 0) (regs 1) (regs 2)
  have he := eval_call_lifted ExecCNFRecords.skipProgram smallRegs onlyCursor a
    smallRegs_injective onlyCursor_injective ht
  simpa only [skipOne, hx, hy, a, b] using he

abbrev peekIndex : Cmd 8 12 := .base (.atom (.peek 2 3 4))
abbrev popIndex : Cmd 8 12 := .base (.atom (.pop 2 3 4))

theorem peekIndex_eval (regs : Fin 8 → Bool)
    (cursor captured index cache selected saved acc : Word) :
    Eval peekIndex 1 (state regs cursor captured index cache selected saved acc)
      (state (readRegs regs 3 4 index.head?) cursor captured index cache selected saved acc) := by
  simpa [peekIndex, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, state]
    using (Eval.base (StructuredProgram.Eval.atom (.peek (2 : Fin 12) (3 : Fin 8) 4)
      (state regs cursor captured index cache selected saved acc)))

theorem popIndex_eval (regs : Fin 8 → Bool) (bit : Bool)
    (cursor captured index cache selected saved acc : Word) :
    Eval popIndex 1 (state regs cursor captured (bit :: index) cache selected saved acc)
      (state (readRegs regs 3 4 (some bit)) cursor captured index cache selected saved acc) := by
  have hs : Function.update
      (![cursor,captured,bit::index,[],[],[],[],cache,selected,[],saved,acc] : Fin 12 → Word)
      2 index = ![cursor,captured,index,[],[],[],[],cache,selected,[],saved,acc] := by
    funext i; fin_cases i <;> rfl
  simpa [popIndex, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, state, hs]
    using (Eval.base (StructuredProgram.Eval.atom (.pop (2 : Fin 12) (3 : Fin 8) 4)
      (state regs cursor captured (bit :: index) cache selected saved acc)))

local infixr:60 " ;; " => Cmd.seq

abbrev skipLoop : Cmd 8 12 := .while 4 (popIndex ;; skipOne ;; peekIndex)
abbrev skipPrefix : Cmd 8 12 := peekIndex ;; skipLoop

def skipCost (before : List Word) : ℕ :=
  5 * (before.map List.length).sum + 11 * before.length + 2

theorem skipLoop_eval (before after : List Word) (regs : Fin 8 → Bool)
    (index cache saved acc : Word) (hi : index.length = before.length)
    (hg : regs 4 = !before.isEmpty) :
    ∃ rf, Eval skipLoop (skipCost before - 1)
      (state regs (ProgramEncoding.encodeRecords (before ++ after)) [] index cache [] saved acc)
      (state rf (ProgramEncoding.encodeRecords after) [] [] cache [] saved acc) := by
  induction before generalizing regs index with
  | nil =>
    have he : index = [] := List.length_eq_zero_iff.mp hi
    subst index
    refine ⟨regs, ?_⟩
    simpa [skipCost, skipLoop] using
      (Eval.while_false (body := popIndex ;; skipOne ;; peekIndex)
        (a := state regs (ProgramEncoding.encodeRecords after) [] [] cache [] saved acc) hg)
  | cons bits before ih =>
    cases index with
    | nil => simp at hi
    | cons bit index =>
      have hi' : index.length = before.length := by simpa using hi
      let r1 := readRegs regs 3 4 (some bit)
      let r2 := skippedRegs r1
      let r3 := readRegs r2 3 4 index.head?
      have hp := popIndex_eval regs bit
        (ProgramEncoding.encodeRecords ((bits :: before) ++ after)) [] index cache [] saved acc
      have hs := skipOne_eval r1 bits (ProgramEncoding.encodeRecords (before ++ after))
        [] index cache [] saved acc
      have he := peekIndex_eval r2 (ProgramEncoding.encodeRecords (before ++ after))
        [] index cache [] saved acc
      have h3 : r3 4 = !before.isEmpty := by
        cases index <;> cases before <;> simp_all [r3, readRegs]
      obtain ⟨rf, ht⟩ := ih r3 index hi' h3
      refine ⟨rf, ?_⟩
      have hb : Eval (popIndex ;; skipOne ;; peekIndex)
          (1 + (5 * bits.length + 8 + 1))
          (state regs (ProgramEncoding.encodeRecords ((bits :: before) ++ after))
            [] (bit :: index) cache [] saved acc)
          (state r3 (ProgramEncoding.encodeRecords (before ++ after)) [] index cache [] saved acc) := by
        simpa only [r1, r2, r3, List.cons_append, ProgramEncoding.encodeRecords,
          Encoding.encodeList, id_eq] using hp.seq (hs.seq he)
      have hr := Eval.while_true
        (by simpa only [state, List.isEmpty_cons, Bool.not_false] using hg) hb ht
      have hcost : 1 + (5 * bits.length + 8 + 1) + (skipCost before - 1) + 1 =
          skipCost (bits :: before) - 1 := by
        simp [skipCost]
        omega
      simpa only [skipLoop, hcost] using hr

theorem skipPrefix_eval (before after : List Word) (regs : Fin 8 → Bool)
    (index cache saved acc : Word) (hi : index.length = before.length) :
    ∃ rf, Eval skipPrefix (skipCost before)
      (state regs (ProgramEncoding.encodeRecords (before ++ after)) [] index cache [] saved acc)
      (state rf (ProgramEncoding.encodeRecords after) [] [] cache [] saved acc) := by
  have hp := peekIndex_eval regs (ProgramEncoding.encodeRecords (before ++ after))
    [] index cache [] saved acc
  have hg : (readRegs regs 3 4 index.head?) 4 = !before.isEmpty := by
    cases index <;> cases before <;> simp_all [readRegs]
  obtain ⟨rf, ht⟩ := skipLoop_eval before after (readRegs regs 3 4 index.head?) index cache saved acc hi hg
  refine ⟨rf, ?_⟩
  have hcost : 1 + (skipCost before - 1) = skipCost before := by
    unfold skipCost
    omega
  simpa only [skipPrefix, hcost] using hp.seq ht

def readerPorts : RecordPrograms.Ports 8 12 :=
  ⟨0, 1, 2, 0, 1, by decide, by decide, by decide, by decide⟩

abbrev capture : Cmd 8 12 :=
  .base (.atom (.pop 0 0 1)) ;; RecordPrograms.reader readerPorts

theorem capture_eval (regs : Fin 8 → Bool) (bits tail cache saved acc : Word) :
    ∃ rf, Eval capture (6 * bits.length + 5)
      (state regs (true :: (Encoding.frame bits ++ tail)) [] [] cache [] saved acc)
      (state rf tail bits.reverse [] cache [] saved acc) := by
  let a := state regs (true :: (Encoding.frame bits ++ tail)) [] [] cache [] saved acc
  let b := state (readRegs regs 0 1 (some true)) (Encoding.frame bits ++ tail) [] [] cache [] saved acc
  have hp : Eval (.base (.atom (.pop 0 0 1))) 1 a b := by
    have hs : Function.update a.stacks 0 (Encoding.frame bits ++ tail) = b.stacks := by
      funext i; fin_cases i <;> rfl
    have he := Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 12) (0 : Fin 8) 1) a)
    change Eval (.base (.atom (.pop 0 0 1))) 1 a
      ⟨readRegs regs 0 1 (some true), Function.update a.stacks 0 (Encoding.frame bits ++ tail)⟩ at he
    rw [hs] at he
    exact he
  have hr := RecordPrograms.reader_eval readerPorts b bits tail [] (b.regs 0) (b.regs 1) (b.regs 2)
  have hstart : RecordPrograms.state readerPorts b (b.regs 0) (b.regs 1) (b.regs 2)
      (Encoding.frame bits ++ tail) [] = b :=
    RecordPrograms.state_eq_self readerPorts b _ _ _ _ _ rfl rfl rfl rfl rfl
  let rf := Function.update (Function.update (Function.update b.regs 0 false) 1 true) 2 (b.regs 2)
  have hend : RecordPrograms.state readerPorts b false true (b.regs 2) tail bits.reverse =
      state rf tail bits.reverse [] cache [] saved acc := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [ readerPorts, b, state]
  rw [hstart] at hr
  simp only [List.append_nil] at hr
  rw [hend] at hr
  exact ⟨rf, by simpa only [capture, Nat.add_comm 1] using hp.seq hr⟩

abbrev command : Cmd 8 12 :=
  .call (StackRoutines.copyProgram 7 0 4 (0 : Fin 8) 1) ;;
  skipPrefix ;; capture ;;
  .call (StackRoutines.clearProgram 0 (0 : Fin 8) 1) ;;
  .call (StackRoutines.transferProgram 1 8 (0 : Fin 8) 1) ;;
  SelectorPairProgram.framePair

def program := compiled command 2 11

def cost (before : List Word) (coefficients : Word) (after : List Word) (saved : Word) : ℕ :=
  7 * (ProgramEncoding.encodeRecords (before ++ coefficients :: after)).length + 5 +
    (skipCost before + (6 * coefficients.length + 5 +
      (2 * (ProgramEncoding.encodeRecords after).length + 3 +
        (3 * coefficients.length + 3 + SelectorPairProgram.frameCost saved coefficients)))) + 1

/-- A real record-skipping loop selects the coefficient payload. The label is
specified by its length, so no canonical unary-bit values are required. -/
theorem program_trace (before : List Word) (coefficients : Word) (after : List Word)
    (saved index acc : Word) (hi : index.length = before.length) (regs : Fin 8 → Bool) :
    ∃ rf, Trace program (cost before coefficients after saved)
      ((state regs [] [] index
        (ProgramEncoding.encodeRecords (before ++ coefficients :: after)) [] saved.reverse acc).withPC
          (some program.entry))
      ((state rf [] [] []
        (ProgramEncoding.encodeRecords (before ++ coefficients :: after)) [] []
        (TupleProgram.prependRecord (SelectorPairProgram.payload saved coefficients) acc)).withPC none) := by
  let cache := ProgramEncoding.encodeRecords (before ++ coefficients :: after)
  let a := state regs [] [] index cache [] saved.reverse acc
  let r1 := readRegs regs 0 1 none
  let b := state r1 cache [] index cache [] saved.reverse acc
  have hc := TupleProgram.copy_eval (7 : Fin 12) 0 4 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a (by rfl)
  have hcopy : Eval (.call (StackRoutines.copyProgram 7 0 4 (0 : Fin 8) 1))
      (7 * cache.length + 5) a b := by
    convert hc using 1
    · simp [a, state]
    · apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i; fin_cases i <;> simp [a, state, StackRoutines.copyStacks]
  obtain ⟨r2, hs⟩ := skipPrefix_eval before (coefficients :: after) r1 index cache saved.reverse acc hi
  obtain ⟨r3, hr⟩ := capture_eval r2 coefficients (ProgramEncoding.encodeRecords after) cache saved.reverse acc
  let d := state r3 (ProgramEncoding.encodeRecords after) coefficients.reverse [] cache [] saved.reverse acc
  let r4 := readRegs r3 0 1 none
  let e := state r4 [] coefficients.reverse [] cache [] saved.reverse acc
  have hclear := TupleProgram.clear_eval (0 : Fin 12) (0 : Fin 8) 1 d
  have hclear' : Eval (.call (StackRoutines.clearProgram 0 (0 : Fin 8) 1))
      (2 * (ProgramEncoding.encodeRecords after).length + 3) d e := by
    convert hclear using 1
    · simp [d, state]
    · apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i; fin_cases i <;> simp [d, state, StackRoutines.clearStacks]
  let r5 := readRegs r4 0 1 none
  let f := state r5 [] [] [] cache coefficients saved.reverse acc
  have hm := TupleProgram.transfer_eval (1 : Fin 12) 8 (0 : Fin 8) 1
    (by decide) (by decide) e
  have hmove : Eval (.call (StackRoutines.transferProgram 1 8 (0 : Fin 8) 1))
      (3 * coefficients.length + 3) e f := by
    convert hm using 1
    · simp [e, state]
    · apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i; fin_cases i <;> simp [e, state, StackRoutines.transferStacks]
  obtain ⟨rf, hf⟩ := SelectorPairProgram.framePair_eval r5 cache saved coefficients acc
  have hall := hcopy.seq (hs.seq (hr.seq (hclear'.seq (hmove.seq hf))))
  have ht := compiled_halt_trace hall (2 : Fin 12) 11
  exact ⟨rf, by simpa only [program, command, cost, cache, a, b, d, e, f, r1,
    state, SelectorPairProgram.state, ProgramEncoding.encodeRecords, Encoding.encodeList,
    List.cons_append, id_eq] using ht⟩

theorem program_primitive (before : List Word) (coefficients : Word) (after : List Word)
    (saved index acc : Word) (hi : index.length = before.length) (regs : Fin 8 → Bool) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * cost before coefficients after saved)
      (BitProgram.primitiveCfg program
        ((state regs [] [] index
          (ProgramEncoding.encodeRecords (before ++ coefficients :: after)) [] saved.reverse acc).withPC
            (some program.entry)))
      (BitProgram.primitiveCfg program
        ((state rf [] [] []
          (ProgramEncoding.encodeRecords (before ++ coefficients :: after)) [] []
          (TupleProgram.prependRecord (SelectorPairProgram.payload saved coefficients) acc)).withPC none)) := by
  obtain ⟨rf, ht⟩ := program_trace before coefficients after saved index acc hi regs
  exact ⟨rf, BitProgram.primitive_trace program ht⟩

end SubexponentialSAT.Subexp.LagrangePacketProgram

end OAI.Algorithms
