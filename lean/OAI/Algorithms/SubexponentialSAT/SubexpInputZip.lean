import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDotControl
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram

namespace OAI.Algorithms

/-!
# Physical pairing of row and input-coordinate streams

Two ordinary framed lists are read on stacks 0 and 1. The fixed program builds
the exact paired-record stream consumed by `SubexpDotControl`, on stack 6.
No array lookup, pairing, or serialization is a semantic machine instruction.
-/

namespace SubexponentialSAT.SubexpInputZip

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 8 8

abbrev state (regs : Fin 8 → Bool)
    (row input left right pair acc output tmp : List Bool) : Data :=
  ⟨regs, ![row, input, left, right, pair, acc, output, tmp]⟩

abbrev ready (regs : Fin 8 → Bool) (row input acc output : List Bool) : Data :=
  state regs row input [] [] [] acc output []

def regPorts (i : Fin 3) : Fin 8 := i.castAdd 5
def writerPorts : Fin 4 → Fin 8 := ![0, 1, 4, 7]

theorem regPorts_injective : Function.Injective regPorts := Fin.castAdd_injective _ _
theorem writerPorts_injective : Function.Injective writerPorts := by decide

abbrev writer : Cmd 8 8 := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram regPorts writerPorts)

def finishedRegs (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update regs 0 true) 1 false

def afterWriter (d : Data) (bits : List Bool) : Data :=
  ⟨finishedRegs d.regs, Function.update (Function.update d.stacks 7 []) 4
    (true :: (Encoding.frame bits ++ d.stacks 4))⟩

theorem writer_data_eval (d : Data) (bits : List Bool)
    (hs : d.stacks 7 = bits.reverse) :
    Eval writer (5 * bits.length + 7) d (afterWriter d bits) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks 0) (d.stacks 1) (d.stacks 4) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks 0) (d.stacks 1) (true :: (Encoding.frame bits ++ d.stacks 4)) []
  have ha : embedState regPorts writerPorts d a = d := by
    apply embedState_eq _ _ regPorts_injective writerPorts_injective
    · intro i; fin_cases i <;> rfl
    · intro i
      fin_cases i <;> simp [a, writerPorts, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, hs]
    · intros; rfl
    · intros; rfl
  have hb : embedState regPorts writerPorts d b = afterWriter d bits := by
    apply embedState_eq _ _ regPorts_injective writerPorts_injective
    · intro i
      fin_cases i <;> simp [afterWriter, finishedRegs, regPorts, b,
        SubexpNormalizeProgram.filterState, SubexpPostfixControl.triple]
    · intro i
      fin_cases i <;> simp [afterWriter, writerPorts, b,
        SubexpNormalizeProgram.filterState, SubexpPostfixControl.quadruple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      simp [afterWriter, finishedRegs, h0, h1]
    · intro i hi
      have h7 : i ≠ 7 := fun h => hi ⟨3, h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨2, h.symm⟩
      simp [afterWriter, h7, h4]
  have ht := SubexpNormalizeProgram.emitRecord_trace bits (d.stacks 0) (d.stacks 1)
    (d.stacks 4) (d.regs 0) (d.regs 1) (d.regs 2)
  have h := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram regPorts writerPorts d
    regPorts_injective writerPorts_injective ht
  change Eval _ _ (embedState _ _ d a) (embedState _ _ d b) at h
  simpa only [writer, ha, hb] using h

theorem writer_eval (regs : Fin 8 → Bool)
    (row input left right pair acc output bits : List Bool) :
    Eval writer (5 * bits.length + 7)
      (state regs row input left right pair acc output bits)
      (state (finishedRegs regs) row input left right
        (true :: (Encoding.frame bits.reverse ++ pair)) acc output []) := by
  have h := writer_data_eval (state regs row input left right pair acc output bits) bits.reverse
    (by simp [])
  have he : afterWriter (state regs row input left right pair acc output bits) bits.reverse =
      state (finishedRegs regs) row input left right
        (true :: (Encoding.frame bits.reverse ++ pair)) acc output [] := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i; fin_cases i <;> rfl
  simpa only [he, List.length_reverse] using h

abbrev move (src dst : Fin 8) : Cmd 8 8 := .call (StackRoutines.transferProgram src dst 0 1)

abbrev popPair : Cmd 8 8 := .base (.atom (.pop 4 0 1))

theorem popPair_eval (regs : Fin 8 → Bool)
    (row input left right pair acc output tmp : List Bool) :
    Eval popPair 1 (state regs row input left right (true :: pair) acc output tmp)
      (state (readRegs regs 0 1 (some true)) row input left right pair acc output tmp) := by
  have h := StructuredProgram.Eval.atom (.pop (4 : Fin 8) (0 : Fin 8) 1)
    (state regs row input left right (true :: pair) acc output tmp)
  have hs : Function.update (![row,input,left,right,true::pair,acc,output,tmp] : Fin 8 → List Bool)
      4 pair = ![row,input,left,right,pair,acc,output,tmp] := by
    funext i; fin_cases i <;> rfl
  apply Eval.base
  simpa [popPair, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, state, hs] using h

theorem move_right (regs : Fin 8 → Bool)
    (row input left right pair acc output : List Bool) :
    Eval (move 3 7) (3 * right.length + 3)
      (state regs row input left right pair acc output [])
      (state (readRegs regs 0 1 none) row input left [] pair acc output right.reverse) := by
  have h := transfer_eval (state regs row input left right pair acc output []) 3 7 0 1
    (by decide) (by decide)
  have he : afterTransfer (state regs row input left right pair acc output []) 3 7 0 1 =
      state (readRegs regs 0 1 none) row input left [] pair acc output right.reverse := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTransfer, StackRoutines.transferStacks]
  change Eval (move 3 7) (3 * right.length + 3)
    (state regs row input left right pair acc output []) _ at h
  simpa only [he] using h

theorem move_left (regs : Fin 8 → Bool)
    (row input left right pair acc output : List Bool) :
    Eval (move 2 7) (3 * left.length + 3)
      (state regs row input left right pair acc output [])
      (state (readRegs regs 0 1 none) row input [] right pair acc output left.reverse) := by
  have h := transfer_eval (state regs row input left right pair acc output []) 2 7 0 1
    (by decide) (by decide)
  have he : afterTransfer (state regs row input left right pair acc output []) 2 7 0 1 =
      state (readRegs regs 0 1 none) row input [] right pair acc output left.reverse := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTransfer, StackRoutines.transferStacks]
  change Eval (move 2 7) (3 * left.length + 3)
    (state regs row input left right pair acc output []) _ at h
  simpa only [he] using h

theorem move_pair (regs : Fin 8 → Bool)
    (row input left right pair acc output : List Bool) :
    Eval (move 4 5) (3 * pair.length + 3)
      (state regs row input left right pair acc output [])
      (state (readRegs regs 0 1 none) row input left right [] (pair.reverse ++ acc) output []) := by
  have h := transfer_eval (state regs row input left right pair acc output []) 4 5 0 1
    (by decide) (by decide)
  have he : afterTransfer (state regs row input left right pair acc output []) 4 5 0 1 =
      state (readRegs regs 0 1 none) row input left right [] (pair.reverse ++ acc) output [] := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTransfer, StackRoutines.transferStacks]
  change Eval (move 4 5) (3 * pair.length + 3)
    (state regs row input left right pair acc output []) _ at h
  simpa only [he] using h

def record (left right : List Bool) : List Bool :=
  true :: (Encoding.frame left.reverse ++ Encoding.frame right.reverse)

theorem record_length (left right : List Bool) :
    (record left right).length = 2 * left.length + 2 * right.length + 3 := by
  simp [record, Encoding.length_frame]
  omega

abbrev pairCommand : Cmd 8 8 :=
  .seq (SubexpInputFrames.readField 0 2 (by decide))
    (.seq (SubexpInputFrames.readField 1 3 (by decide))
      (.seq (move 3 7) (.seq writer (.seq popPair
        (.seq (move 2 7) (.seq writer (move 4 5)))))))

theorem pair_execute (regs : Fin 8 → Bool)
    (left right rowTail inputTail acc output : List Bool) :
    ∃ rf, Eval pairCommand (20 * left.length + 20 * right.length + 41)
      (ready regs (Encoding.frame left ++ rowTail) (Encoding.frame right ++ inputTail) acc output)
      (ready rf rowTail inputTail ((record left right).reverse ++ acc) output) := by
  let d := ready regs (Encoding.frame left ++ rowTail) (Encoding.frame right ++ inputTail) acc output
  obtain ⟨e₁, h₁, hs₁⟩ := SubexpInputFrames.readField_execute 0 2 (by decide) d left rowTail rfl rfl
  have he₁ : e₁ = state e₁.regs rowTail (Encoding.frame right ++ inputTail)
      left.reverse [] [] acc output [] := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · rw [hs₁]; funext i; fin_cases i <;> rfl
  obtain ⟨e₂, h₂, hs₂⟩ := SubexpInputFrames.readField_execute 1 3 (by decide)
    e₁ right inputTail (by rw [he₁]; rfl) (by rw [he₁]; rfl)
  have he₂ : e₂ = state e₂.regs rowTail inputTail left.reverse right.reverse [] acc output [] := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · rw [hs₂, he₁]; funext i; fin_cases i <;> rfl
  rw [he₁] at h₁ h₂
  rw [he₂] at h₂
  let r₃ := readRegs e₂.regs 0 1 none
  let r₄ := finishedRegs r₃
  let r₅ := readRegs r₄ 0 1 (some true)
  let r₆ := readRegs r₅ 0 1 none
  let r₇ := finishedRegs r₆
  have h₃ := move_right e₂.regs rowTail inputTail left.reverse right.reverse [] acc output
  simp only [List.length_reverse, List.reverse_reverse] at h₃
  have h₄ := writer_eval r₃ rowTail inputTail left.reverse [] [] acc output right
  simp only [List.append_nil] at h₄
  have h₅ := popPair_eval r₄ rowTail inputTail left.reverse [] (Encoding.frame right.reverse) acc output []
  have h₆ := move_left r₅ rowTail inputTail left.reverse [] (Encoding.frame right.reverse) acc output
  simp only [List.length_reverse, List.reverse_reverse] at h₆
  have h₇ := writer_eval r₆ rowTail inputTail [] [] (Encoding.frame right.reverse) acc output left
  have h₈ := move_pair r₇ rowTail inputTail [] [] (record left right) acc output
  rw [record_length] at h₈
  have h := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ (Eval.seq h₄
    (Eval.seq h₅ (Eval.seq h₆ (Eval.seq h₇ h₈))))))
  refine ⟨readRegs r₇ 0 1 none, ?_⟩
  have hc : 6 * left.length + 4 + (6 * right.length + 4 +
      (3 * right.length + 3 + (5 * right.length + 7 + (1 +
        (3 * left.length + 3 + (5 * left.length + 7 +
          (3 * (2 * left.length + 2 * right.length + 3) + 3))))))) =
      20 * left.length + 20 * right.length + 41 := by omega
  simpa only [pairCommand, hc] using h

abbrev tags : Cmd 8 8 :=
  .seq (SubexpInputFrames.readTag 0) (.base (.atom (.pop 1 0 1)))

theorem tags_execute (regs : Fin 8 → Bool) (flag : Bool)
    (row input acc output : List Bool) :
    ∃ rf, Eval tags 2 (ready regs (flag :: row) (flag :: input) acc output)
      (ready rf row input acc output) ∧ rf 7 = flag := by
  let d := ready regs (flag :: row) (flag :: input) acc output
  obtain ⟨e, he, hs, hf⟩ := SubexpInputFrames.readTag_execute 0 d flag row rfl
  have heq : e = ready e.regs row (flag :: input) acc output := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · rw [hs]; funext i; fin_cases i <;> rfl
  let rf := readRegs e.regs 0 1 (some flag)
  have hp : Eval (.base (.atom (.pop 1 0 1))) 1
      (ready e.regs row (flag :: input) acc output) (ready rf row input acc output) := by
    have h := StructuredProgram.Eval.atom (.pop (1 : Fin 8) (0 : Fin 8) 1)
      (ready e.regs row (flag :: input) acc output)
    have ht : Function.update (![row,flag::input,[],[],[],acc,output,[]] : Fin 8 → List Bool)
        1 input = ![row,input,[],[],[],acc,output,[]] := by
      funext i; fin_cases i <;> rfl
    apply Eval.base
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, state, ready, rf, ht] using h
  refine ⟨rf, ?_, ?_⟩
  · rw [heq] at he
    exact Eval.seq he hp
  · simpa [rf, readRegs] using hf

abbrev loop : Cmd 8 8 := .while 7 (.seq pairCommand tags)

def rowWords (pairs : List (List Bool × List Bool)) : List (List Bool) := pairs.map Prod.fst
def inputWords (pairs : List (List Bool × List Bool)) : List (List Bool) := pairs.map Prod.snd

def rowAfter : List (List Bool × List Bool) → List Bool → List Bool
  | [], suffix => suffix
  | (left, _) :: rest, suffix => Encoding.frame left ++ Encoding.encodeList id (rowWords rest) ++ suffix

def inputAfter : List (List Bool × List Bool) → List Bool → List Bool
  | [], suffix => suffix
  | (_, right) :: rest, suffix => Encoding.frame right ++ Encoding.encodeList id (inputWords rest) ++ suffix

theorem row_tag (pairs : List (List Bool × List Bool)) (suffix : List Bool) :
    Encoding.encodeList id (rowWords pairs) ++ suffix =
      SubexpDotControl.listFlag pairs :: rowAfter pairs suffix := by
  cases pairs <;> simp [rowWords, Encoding.encodeList, rowAfter, SubexpDotControl.listFlag, List.append_assoc]

theorem input_tag (pairs : List (List Bool × List Bool)) (suffix : List Bool) :
    Encoding.encodeList id (inputWords pairs) ++ suffix =
      SubexpDotControl.listFlag pairs :: inputAfter pairs suffix := by
  cases pairs <;> simp [inputWords, Encoding.encodeList, inputAfter, SubexpDotControl.listFlag, List.append_assoc]

def pairBody : List (List Bool × List Bool) → List Bool
  | [] => []
  | (left, right) :: rest => record left right ++ pairBody rest

def inputBits : List (List Bool × List Bool) → ℕ
  | [] => 0
  | (left, right) :: rest => left.length + right.length + inputBits rest

def scanCost : List (List Bool × List Bool) → ℕ
  | [] => 1
  | (left, right) :: rest => 20 * left.length + 20 * right.length + 44 + scanCost rest

theorem pairBody_length (pairs : List (List Bool × List Bool)) :
    (pairBody pairs).length = 2 * inputBits pairs + 3 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨left, right⟩
    simp only [pairBody, List.length_append, record_length, inputBits, List.length_cons, ih]
    omega

theorem scanCost_eq (pairs : List (List Bool × List Bool)) :
    scanCost pairs = 20 * inputBits pairs + 44 * pairs.length + 1 := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨left, right⟩
    simp only [scanCost, inputBits, List.length_cons, ih]
    omega

theorem pairBody_encodePairs (pairs : List (List Bool × List Bool)) :
    pairBody pairs ++ [false] = SubexpDotControl.encodePairs id pairs := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨left, right⟩
    simp only [pairBody, record, List.cons_append, List.append_assoc, ih,
      SubexpDotControl.encodePairs, SubexpDotControl.payload, id_eq]

theorem loop_execute (pairs : List (List Bool × List Bool)) (regs : Fin 8 → Bool)
    (rowSuffix inputSuffix acc output : List Bool)
    (hf : regs 7 = SubexpDotControl.listFlag pairs) :
    ∃ rf, Eval loop (scanCost pairs)
      (ready regs (rowAfter pairs rowSuffix) (inputAfter pairs inputSuffix) acc output)
      (ready rf rowSuffix inputSuffix ((pairBody pairs).reverse ++ acc) output) := by
  induction pairs generalizing regs acc with
  | nil =>
    refine ⟨regs, ?_⟩
    have h : Eval loop 1 (ready regs rowSuffix inputSuffix acc output)
        (ready regs rowSuffix inputSuffix acc output) := .while_false hf
    simpa only [scanCost, rowAfter, inputAfter, pairBody, List.reverse_nil, List.nil_append]
      using h
  | cons pair rest ih =>
    rcases pair with ⟨left, right⟩
    obtain ⟨rp, hp⟩ := pair_execute regs left right
      (Encoding.encodeList id (rowWords rest) ++ rowSuffix)
      (Encoding.encodeList id (inputWords rest) ++ inputSuffix) acc output
    obtain ⟨rt, ht, hft⟩ := tags_execute rp (SubexpDotControl.listFlag rest)
      (rowAfter rest rowSuffix) (inputAfter rest inputSuffix) ((record left right).reverse ++ acc) output
    rw [← row_tag, ← input_tag] at ht
    obtain ⟨rf, htail⟩ := ih rt ((record left right).reverse ++ acc) hft
    refine ⟨rf, ?_⟩
    have h := Eval.while_true hf (Eval.seq hp ht) htail
    simpa only [loop, scanCost, rowAfter, inputAfter, pairBody, List.reverse_append,
      List.append_assoc, show 20 * left.length + 20 * right.length + 41 + 2 + scanCost rest + 1 =
        20 * left.length + 20 * right.length + 44 + scanCost rest by omega] using h

abbrev finish : Cmd 8 8 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.push 5 0))) (move 5 6))

theorem finish_execute (regs : Fin 8 → Bool) (row input acc output : List Bool) :
    ∃ rf, Eval finish (3 * acc.length + 8) (ready regs row input acc output)
      (ready rf row input [] (acc.reverse ++ [false] ++ output)) := by
  let r₁ := Function.update regs 0 false
  have h₁ : Eval (.base (.atom (.set 0 false))) 1 (ready regs row input acc output)
      (ready r₁ row input acc output) := by
    exact Eval.base (.atom _ _)
  have h₂ : Eval (.base (.atom (.push 5 0))) 1 (ready r₁ row input acc output)
      (ready r₁ row input (false :: acc) output) := by
    have h := StructuredProgram.Eval.atom (.push (5 : Fin 8) (0 : Fin 8))
      (ready r₁ row input acc output)
    have hs : Function.update (![row,input,[],[],[],acc,output,[]] : Fin 8 → List Bool)
        5 (false :: acc) = ![row,input,[],[],[],false::acc,output,[]] := by
      funext i; fin_cases i <;> rfl
    apply Eval.base
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, state, ready, r₁, hs] using h
  have h₃ := transfer_eval (ready r₁ row input (false :: acc) output) 5 6 0 1
    (by decide) (by decide)
  have he : afterTransfer (ready r₁ row input (false :: acc) output) 5 6 0 1 =
      ready (readRegs r₁ 0 1 none) row input [] (acc.reverse ++ [false] ++ output) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTransfer,
        StackRoutines.transferStacks, List.reverse_cons, List.append_assoc]
  refine ⟨readRegs r₁ 0 1 none, ?_⟩
  have hlen : ((ready r₁ row input (false :: acc) output).stacks 5).length = acc.length + 1 := rfl
  rw [hlen, he] at h₃
  have h := Eval.seq h₁ (Eval.seq h₂ h₃)
  simpa only [finish, move,
    show 1 + (1 + (3 * (acc.length + 1) + 3)) = 3 * acc.length + 8 by omega] using h

abbrev command : Cmd 8 8 := .seq tags (.seq loop finish)
abbrev program : Program 8 8 (size command + 1) := compiled command 0 6

theorem program_labels : size command + 1 = 73 := by rfl

theorem program_trace (pairs : List (List Bool × List Bool)) (regs : Fin 8 → Bool)
    (rowSuffix inputSuffix outputSuffix : List Bool) :
    ∃ rf, Trace program (26 * inputBits pairs + 53 * pairs.length + 12)
      ((ready regs (Encoding.encodeList id (rowWords pairs) ++ rowSuffix)
        (Encoding.encodeList id (inputWords pairs) ++ inputSuffix) [] outputSuffix).withPC
          (some program.entry))
      ((ready rf rowSuffix inputSuffix []
        (SubexpDotControl.encodePairs id pairs ++ outputSuffix)).withPC none) := by
  obtain ⟨rt, ht, hft⟩ := tags_execute regs (SubexpDotControl.listFlag pairs)
    (rowAfter pairs rowSuffix) (inputAfter pairs inputSuffix) [] outputSuffix
  rw [← row_tag, ← input_tag] at ht
  obtain ⟨rl, hl⟩ := loop_execute pairs rt rowSuffix inputSuffix [] outputSuffix hft
  simp only [List.append_nil] at hl
  obtain ⟨rf, hf⟩ := finish_execute rl rowSuffix inputSuffix (pairBody pairs).reverse outputSuffix
  simp only [List.length_reverse, List.reverse_reverse, pairBody_encodePairs] at hf
  have h := compiled_halt_trace (Eval.seq ht (Eval.seq hl hf)) 0 6
  refine ⟨rf, ?_⟩
  have hc : 2 + (scanCost pairs + (3 * (pairBody pairs).length + 8)) + 1 =
      26 * inputBits pairs + 53 * pairs.length + 12 := by
    rw [scanCost_eq, pairBody_length]
    omega
  simpa only [program, command, hc] using h

def rawPairs {C : Type*} (encode : C → List Bool) (pairs : List (C × C)) :
    List (List Bool × List Bool) := pairs.map (fun pair => (encode pair.1, encode pair.2))

theorem encodeList_map {C : Type*} (encode : C → List Bool) (xs : List C) :
    Encoding.encodeList id (xs.map encode) = Encoding.encodeList encode xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Encoding.encodeList, id_eq, ih]

theorem rawPairs_encode {C : Type*} (encode : C → List Bool) (pairs : List (C × C)) :
    SubexpDotControl.encodePairs id (rawPairs encode pairs) =
      SubexpDotControl.encodePairs encode pairs := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    simp only [rawPairs, List.map_cons, SubexpDotControl.encodePairs,
      SubexpDotControl.payload, id_eq] at *
    rw [ih]

theorem inputBits_rawPairs {C : Type*} (encode : C → List Bool) (K : ℕ)
    (hlen : ∀ x, (encode x).length = K) (pairs : List (C × C)) :
    inputBits (rawPairs encode pairs) = 2 * K * pairs.length := by
  induction pairs with
  | nil => simp [rawPairs, inputBits]
  | cons pair rest ih =>
    simp only [rawPairs, List.map_cons, inputBits, hlen] at *
    rw [ih, List.length_cons]
    ring

/-- The zipper consumes two separate input streams and produces the exact
paired stream used by the arithmetic loop, with a linear transition count. -/
theorem program_encoded_trace {C : Type*} (encode : C → List Bool) (K : ℕ)
    (hlen : ∀ x, (encode x).length = K) (pairs : List (C × C))
    (regs : Fin 8 → Bool) (rowSuffix inputSuffix outputSuffix : List Bool) :
    ∃ rf, Trace program (pairs.length * (52 * K + 53) + 12)
      ((ready regs (Encoding.encodeList encode (pairs.map Prod.fst) ++ rowSuffix)
        (Encoding.encodeList encode (pairs.map Prod.snd) ++ inputSuffix) [] outputSuffix).withPC
          (some program.entry))
      ((ready rf rowSuffix inputSuffix []
        (SubexpDotControl.encodePairs encode pairs ++ outputSuffix)).withPC none) := by
  obtain ⟨rf, h⟩ := program_trace (rawPairs encode pairs) regs rowSuffix inputSuffix outputSuffix
  rw [rawPairs_encode, inputBits_rawPairs encode K hlen] at h
  have hr : rowWords (rawPairs encode pairs) = (pairs.map Prod.fst).map encode := by
    simp [rowWords, rawPairs, List.map_map, Function.comp_def]
  have hi : inputWords (rawPairs encode pairs) = (pairs.map Prod.snd).map encode := by
    simp [inputWords, rawPairs, List.map_map, Function.comp_def]
  rw [hr, hi, encodeList_map, encodeList_map] at h
  have hc : 26 * (2 * K * pairs.length) + 53 * (rawPairs encode pairs).length + 12 =
      pairs.length * (52 * K + 53) + 12 := by
    simp only [rawPairs, List.length_map]
    ring
  exact ⟨rf, hc ▸ h⟩

theorem program_rows_trace {D B : ℕ} {C : Type*} (encode : C → List Bool)
    (hlen : ∀ x, (encode x).length = 4 * B) (row x : Fin D → C)
    (regs : Fin 8 → Bool) (rowSuffix inputSuffix outputSuffix : List Bool) :
    ∃ rf, Trace program (D * (52 * (4 * B) + 53) + 12)
      ((ready regs (Encoding.encodeList encode ((List.finRange D).map row) ++ rowSuffix)
        (Encoding.encodeList encode ((List.finRange D).map x) ++ inputSuffix) [] outputSuffix).withPC
          (some program.entry))
      ((ready rf rowSuffix inputSuffix []
        (SubexpDotControl.encodePairs encode (SubexpDotControl.pairsFor row x) ++ outputSuffix)).withPC none) := by
  simpa [SubexpDotControl.pairsFor, List.map_map, Function.comp_def] using program_encoded_trace encode (4 * B) hlen
      (SubexpDotControl.pairsFor row x) regs rowSuffix inputSuffix outputSuffix

theorem program_primitive {C : Type*} (encode : C → List Bool) (K : ℕ)
    (hlen : ∀ x, (encode x).length = K) (pairs : List (C × C))
    (regs : Fin 8 → Bool) (rowSuffix inputSuffix outputSuffix : List Bool) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (pairs.length * (52 * K + 53) + 12))
      (primitiveCfg program
        ((ready regs (Encoding.encodeList encode (pairs.map Prod.fst) ++ rowSuffix)
          (Encoding.encodeList encode (pairs.map Prod.snd) ++ inputSuffix) [] outputSuffix).withPC
            (some program.entry)))
      (primitiveCfg program ((ready rf rowSuffix inputSuffix []
        (SubexpDotControl.encodePairs encode pairs ++ outputSuffix)).withPC none)) := by
  obtain ⟨rf, h⟩ := program_encoded_trace encode K hlen pairs regs rowSuffix inputSuffix outputSuffix
  exact ⟨rf, primitive_trace program h⟩

/-- Explicit polynomial bound for pairing, the dot loop, and canonical lifting
when the target width is (D+1) times the residue-word width. -/
theorem sourceBound_polynomial (D b : ℕ) :
    D * (52 * (4 * b) + 53) + 12 +
      (D * (SubexpDotControl.pairCost b + 2) + 3 +
        2100 * (b + (D + 1) * b + 2)^2 + 1) + 1 ≤
      430000 * (D + 2)^2 * (b + 2)^2 := by
  let T := (D + 2)^2 * (b + 2)^2
  have hb : b ≤ (b + 2)^2 := by nlinarith
  have hb1 : 1 ≤ (b + 2)^2 := by nlinarith
  have hd : D ≤ (D + 2)^2 := by nlinarith
  have hd1 : 1 ≤ (D + 2)^2 := by nlinarith
  have ht : 1 ≤ T := Nat.mul_le_mul hd1 hb1
  have hs := Nat.pow_le_pow_left (show b + 1 ≤ b + 2 by omega) 2
  have hp : 425000 * (b + 1)^2 + 256 * b + 63 ≤ 425319 * (b + 2)^2 := by omega
  have hfirst : D * (425000 * (b + 1)^2 + 256 * b + 63) ≤ 425319 * T := by
    calc
      _ ≤ (D + 2)^2 * (425319 * (b + 2)^2) := Nat.mul_le_mul hd hp
      _ = 425319 * T := by dsimp [T]; ring
  have hlinear : (D + 2) * b + 2 ≤ (D + 2) * (b + 2) := by nlinarith
  have hlift : ((D + 2) * b + 2)^2 ≤ T := by
    simpa only [mul_pow] using Nat.pow_le_pow_left hlinear 2
  calc
    _ = D * (425000 * (b + 1)^2 + 256 * b + 63) +
        2100 * ((D + 2) * b + 2)^2 + 17 := by unfold SubexpDotControl.pairCost; ring
    _ ≤ 425319 * T + 2100 * T + 17 :=
      Nat.add_le_add_right (Nat.add_le_add hfirst (Nat.mul_le_mul_left 2100 hlift)) 17
    _ ≤ 430000 * T := by omega
    _ = _ := by dsimp [T]; ring

end SubexponentialSAT.SubexpInputZip

end OAI.Algorithms
