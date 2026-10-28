import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorCountSetup
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCopyProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Concrete tape operations and traversal assertions for the outer CRT.
All operations in this module are fixed finite programs. Arithmetic is supplied
by the separately defined concrete CRT service commands. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Code := Cmd 16 320

def registers : Fin 8 ↪ Fin 16 := ⟨Fin.castAdd 8, Fin.castAdd_injective 8 8⟩
def threeRegisters : Fin 3 ↪ Fin 16 := ⟨Fin.castAdd 13, Fin.castAdd_injective 3 13⟩
def localPorts : Fin 256 ↪ Fin 320 := ⟨Fin.castAdd 64, Fin.castAdd_injective 256 64⟩

/-- Native multiplication bank 128--204 is shared with local convolution. -/
def scalarPorts : Fin 110 ↪ Fin 320 :=
  ⟨fun i => ⟨128 + i.val, by omega⟩, by
    intro i j h
    apply Fin.ext
    have hv := congrArg (fun x : Fin 320 => x.val) h
    dsimp at hv
    omega⟩

/-- Horner's ten higher ports avoid the constants at 206, 207, and 211. -/
def hornerPort (i : Fin 87) : Fin 320 :=
  if i.val < 77 then ⟨128 + i.val, by omega⟩ else ⟨169 + i.val, by omega⟩

def hornerPorts : Fin 87 ↪ Fin 320 :=
  ⟨hornerPort, by
    intro i j h
    apply Fin.ext
    have hv := congrArg (fun x : Fin 320 => x.val) h
    by_cases hi : i.val < 77 <;> by_cases hj : j.val < 77 <;>
      simp only [hornerPort, hi, hj, ite_true, ite_false] at hv <;> omega⟩

@[simp] theorem hornerPorts_output : hornerPorts 72 = (200 : Fin 320) := rfl
@[simp] theorem hornerPorts_stream : hornerPorts 77 = (246 : Fin 320) := rfl
@[simp] theorem hornerPorts_point : hornerPorts 78 = (247 : Fin 320) := rfl
@[simp] theorem hornerPorts_count : hornerPorts 79 = (248 : Fin 320) := rfl
@[simp] theorem hornerPorts_blockWidth : hornerPorts 81 = (250 : Fin 320) := rfl

def countPorts : Fin 13 ↪ Fin 320 :=
  ⟨![267,243,268,269,316,317,270,271,272,273,274,275,276], by decide⟩

def blockCopyPorts : Fin 4 ↪ Fin 320 := ⟨![104,277,278,279], by decide⟩

private abbrev seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def copy (src dst : Fin 320) : Code :=
  .call (StackRoutines.copyProgram src dst 318 (0 : Fin 16) 1)

def transfer (src dst : Fin 320) : Code :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 16) 1)

def move (src dst : Fin 320) : Code := transfer src 319 ;; transfer 319 dst

def clear (src : Fin 320) : Code :=
  .call (StackRoutines.clearProgram src (0 : Fin 16) 1)

def clearMany : List (Fin 320) → Code
  | [] => .base .skip
  | src :: rest => clear src ;; clearMany rest

def testNodes : Code := .base (.atom (.peek 257 0 15))

def incrementIndex : Code :=
  .base (.seq (.atom (.set 0 false)) (.atom (.push 260 0)))

def resetThreeRegisters : Code :=
  .base (.seq (.atom (.set 0 false))
    (.seq (.atom (.set 1 false)) (.atom (.set 2 false))))

def countDimension : Code :=
  .call (ProgramLinking.liftProgram SubexpFactorCountSetup.countProgram registers countPorts)

def buildJetWidth : Code :=
  copy 243 279 ;; resetThreeRegisters ;;
    .call (ProgramLinking.liftProgram Subexp.BlockCopyProgram.program
      threeRegisters blockCopyPorts)

def initializeOuter : Code :=
  copy 202 278 ;; .call (zeroFillProgram 278 104 (0 : Fin 16) 1) ;;
    copy 202 278 ;; .call (zeroFillProgram 278 261 (0 : Fin 16) 1) ;;
    countDimension ;; buildJetWidth ;; copy 256 214 ;; copy 256 257 ;; copy 265 266

def takeNode : Code := takeWord 104 278 279 257 259 0 1
def takeJet : Code := takeWord 277 278 279 266 225 0 1

def advance : Code :=
  copy 259 258 ;; clearMany [213,216,225,259] ;; incrementIndex

def cleanup : Code := clearMany [104,214,257,258,260,266,268,277]


abbrev Data := State 16 320

theorem copy_run (d : Data) (src dst : Fin 320)
    (hsd : src ≠ dst) (hs : src ≠ 318) (hd : (318 : Fin 320) ≠ dst)
    (ht : d.stacks 318 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d
      (afterCopy d src dst 0 1) :=
  SubexpScanPrimitives.copy_eval d src dst 318 0 1 hsd hs hd (by decide) ht

theorem clear_run (d : Data) (src : Fin 320) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d
      (SubexpSetupStorage.clearState src d) :=
  SubexpSetupStorage.clear_eval src d

theorem clearMany_run (d : Data) (ports : List (Fin 320)) :
    Eval (clearMany ports) (SubexpSetupStorage.clearManyCost ports d) d
      (SubexpSetupStorage.clearManyState ports d) := by
  have he : clearMany ports = SubexpSetupStorage.clearMany ports := by
    induction ports with
    | nil => rfl
    | cons p ps ih =>
      change Cmd.seq (clear p) (clearMany ps) =
        Cmd.seq (SubexpSetupStorage.clearCmd p) (SubexpSetupStorage.clearMany ps)
      rw [ih]
      rfl
  rw [he]
  exact SubexpSetupStorage.clearMany_eval ports d

/-- These fields describe physical traversal stacks. Other stacks, including
the scalar bank and retained inputs, are framed by the execution theorems. -/
structure SweepWords where
  remaining : List Bool
  processed : List Bool
  index : List Bool
  accumulator : List Bool
  jets : List Bool
  current : List Bool := []
  nodeCopy : List Bool := []
  indexCopy : List Bool := []
  jet : List Bool := []

def sweepStore (frame : Fin 320 → List Bool) (w : SweepWords) (j : Fin 320) : List Bool :=
  if j = 213 then w.nodeCopy else
  if j = 216 then w.indexCopy else
  if j = 225 then w.jet else
  if j = 257 then w.remaining else
  if j = 258 then w.processed else
  if j = 259 then w.current else
  if j = 260 then w.index else
  if j = 261 then w.accumulator else
  if j = 266 then w.jets else frame j

def sweepState (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool) (w : SweepWords) :
    Data := ⟨regs, sweepStore frame w⟩

@[simp] theorem sweepStore_nodeCopy (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 213 = w.nodeCopy := rfl

@[simp] theorem update_sweepStore_nodeCopy (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 213 bits = sweepStore f {w with nodeCopy := bits} := by
  funext j
  by_cases h : j = (213 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_indexCopy (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 216 = w.indexCopy := rfl

@[simp] theorem update_sweepStore_indexCopy (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 216 bits = sweepStore f {w with indexCopy := bits} := by
  funext j
  by_cases h : j = (216 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_jet (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 225 = w.jet := rfl

@[simp] theorem update_sweepStore_jet (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 225 bits = sweepStore f {w with jet := bits} := by
  funext j
  by_cases h : j = (225 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_remaining (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 257 = w.remaining := rfl

@[simp] theorem update_sweepStore_remaining (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 257 bits = sweepStore f {w with remaining := bits} := by
  funext j
  by_cases h : j = (257 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_processed (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 258 = w.processed := rfl

@[simp] theorem update_sweepStore_processed (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 258 bits = sweepStore f {w with processed := bits} := by
  funext j
  by_cases h : j = (258 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_current (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 259 = w.current := rfl

@[simp] theorem update_sweepStore_current (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 259 bits = sweepStore f {w with current := bits} := by
  funext j
  by_cases h : j = (259 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_index (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 260 = w.index := rfl

@[simp] theorem update_sweepStore_index (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 260 bits = sweepStore f {w with index := bits} := by
  funext j
  by_cases h : j = (260 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_accumulator (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 261 = w.accumulator := rfl

@[simp] theorem update_sweepStore_accumulator (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 261 bits = sweepStore f {w with accumulator := bits} := by
  funext j
  by_cases h : j = (261 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_jets (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 266 = w.jets := rfl

@[simp] theorem update_sweepStore_jets (f : Fin 320 → List Bool) (w : SweepWords)
    (bits : List Bool) :
    Function.update (sweepStore f w) 266 bits = sweepStore f {w with jets := bits} := by
  funext j
  by_cases h : j = (266 : Fin 320)
  · subst j; simp [sweepStore]
  · simp [sweepStore, h]

@[simp] theorem sweepStore_width (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 104 = f 104 := rfl

@[simp] theorem sweepStore_jetWidth (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 277 = f 277 := rfl

@[simp] theorem sweepStore_counter (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 278 = f 278 := rfl

@[simp] theorem sweepStore_takeTmp (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 279 = f 279 := rfl

@[simp] theorem sweepStore_copyTmp (f : Fin 320 → List Bool) (w : SweepWords) :
    sweepStore f w 318 = f 318 := rfl

theorem takeNode_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) (bits rest : List Bool)
    (hs : w.remaining = bits ++ rest) (hc : w.current = [])
    (ht : frame 278 = []) (hu : frame 279 = [])
    (hw : (frame 104).length = bits.length) :
    Eval takeNode (14 * bits.length + 11) (sweepState regs frame w)
      (sweepState (readRegs regs 0 1 none) frame
        {w with remaining := rest, current := bits}) := by
  have h := takeWord_eval (sweepState regs frame w) 104 278 279 257 259 0 1
    (by decide) (by decide) bits rest (by simpa [sweepState] using hs)
    (by simpa [sweepState] using ht) (by simpa [sweepState] using hu)
    (by simpa [sweepState] using hw)
  simpa only [takeNode, afterTake, sweepState, sweepStore_current, hc,
    List.append_nil, update_sweepStore_remaining, update_sweepStore_current] using h

theorem takeJet_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) (bits rest : List Bool)
    (hs : w.jets = bits ++ rest) (hc : w.jet = [])
    (ht : frame 278 = []) (hu : frame 279 = [])
    (hw : (frame 277).length = bits.length) :
    Eval takeJet (14 * bits.length + 11) (sweepState regs frame w)
      (sweepState (readRegs regs 0 1 none) frame
        {w with jets := rest, jet := bits}) := by
  have h := takeWord_eval (sweepState regs frame w) 277 278 279 266 225 0 1
    (by decide) (by decide) bits rest (by simpa [sweepState] using hs)
    (by simpa [sweepState] using ht) (by simpa [sweepState] using hu)
    (by simpa [sweepState] using hw)
  simpa only [takeJet, afterTake, sweepState, sweepStore_jet, hc,
    List.append_nil, update_sweepStore_jets, update_sweepStore_jet] using h

theorem copyCurrent_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) (ht : frame 318 = []) (he : w.nodeCopy = []) :
    Eval (copy 259 213) (7 * w.current.length + 5) (sweepState regs frame w)
      (sweepState (readRegs regs 0 1 none) frame {w with nodeCopy := w.current}) := by
  have h := copy_run (sweepState regs frame w) 259 213
    (by decide) (by decide) (by decide) (by simpa [sweepState] using ht)
  simpa only [afterCopy, sweepState, sweepStore_current, StackRoutines.copyStacks,
    sweepStore_nodeCopy, he, List.append_nil, update_sweepStore_nodeCopy] using h

theorem copyIndex_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) (ht : frame 318 = []) (he : w.indexCopy = []) :
    Eval (copy 260 216) (7 * w.index.length + 5) (sweepState regs frame w)
      (sweepState (readRegs regs 0 1 none) frame {w with indexCopy := w.index}) := by
  have h := copy_run (sweepState regs frame w) 260 216
    (by decide) (by decide) (by decide) (by simpa [sweepState] using ht)
  simpa only [afterCopy, sweepState, sweepStore_index, StackRoutines.copyStacks,
    sweepStore_indexCopy, he, List.append_nil, update_sweepStore_indexCopy] using h

def loadCurrent : Code := takeNode ;; copy 259 213 ;; copy 260 216 ;; takeJet

def loadedWords (w : SweepWords) (node nodes jet jets : List Bool) : SweepWords :=
  {w with
    remaining := nodes
    current := node
    nodeCopy := node
    indexCopy := w.index
    jet := jet
    jets := jets}

/-- Exact physical loading of one node, its index, and its matching padded jet. -/
theorem loadCurrent_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) (node nodes jet jets : List Bool)
    (hn : w.remaining = node ++ nodes) (hj : w.jets = jet ++ jets)
    (hc : w.current = []) (hcopy : w.nodeCopy = [])
    (hi : w.indexCopy = []) (hjet : w.jet = [])
    (ht : frame 278 = []) (hu : frame 279 = []) (hv : frame 318 = [])
    (hw : (frame 104).length = node.length) (hjw : (frame 277).length = jet.length) :
    Eval loadCurrent (21 * node.length + 7 * w.index.length + 14 * jet.length + 32)
      (sweepState regs frame w)
      (sweepState (readRegs regs 0 1 none) frame (loadedWords w node nodes jet jets)) := by
  have h1 := takeNode_run regs frame w node nodes hn hc ht hu hw
  have h2 := copyCurrent_run (readRegs regs 0 1 none) frame
    {w with remaining := nodes, current := node} hv hcopy
  have h3 := copyIndex_run (readRegs regs 0 1 none) frame
    {w with remaining := nodes, current := node, nodeCopy := node} hv hi
  have h4 := takeJet_run (readRegs regs 0 1 none) frame
    {w with remaining := nodes, current := node, nodeCopy := node, indexCopy := w.index}
    jet jets hj hjet ht hu hjw
  simp only [StackRoutines.readRegs_reset] at h2 h3 h4
  have h := h1.seq (h2.seq (h3.seq h4))
  convert h using 1 <;> try rfl
  omega

def cleanedWords (w : SweepWords) : SweepWords :=
  {w with nodeCopy := [], indexCopy := [], jet := [], current := []}

theorem clearCurrent_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) :
    Eval (clearMany [213,216,225,259])
      (2 * w.nodeCopy.length + 2 * w.indexCopy.length + 2 * w.jet.length +
        2 * w.current.length + 12)
      (sweepState regs frame w)
      (sweepState (readRegs regs 0 1 none) frame (cleanedWords w)) := by
  have h := clearMany_run (sweepState regs frame w) [213,216,225,259]
  simp [SubexpSetupStorage.clearManyCost, SubexpSetupStorage.clearManyState,
    SubexpSetupStorage.clearState, sweepState, StackRoutines.readRegs_reset,
    Nat.add_assoc] at h
  convert h using 1 <;> try rfl
  omega

theorem incrementIndex_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) :
    Eval incrementIndex 2 (sweepState regs frame w)
      (sweepState (Function.update regs 0 false) frame {w with index := false :: w.index}) := by
  have h1 := StructuredProgram.Eval.atom (.set (0 : Fin 16) false) (sweepState regs frame w)
  have h2 := StructuredProgram.Eval.atom (.push (260 : Fin 320) (0 : Fin 16))
    ((StructuredProgram.Atom.set 0 false).eval (sweepState regs frame w))
  have h := Eval.base (h1.seq h2)
  simpa [incrementIndex, sweepState, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h

def advancedWords (w : SweepWords) : SweepWords :=
  {cleanedWords w with processed := w.current ++ w.processed, index := false :: w.index}

theorem advance_run (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool)
    (w : SweepWords) (ht : frame 318 = []) :
    Eval advance
      (9 * w.current.length + 2 * w.nodeCopy.length + 2 * w.indexCopy.length +
        2 * w.jet.length + 19)
      (sweepState regs frame w)
      (sweepState (Function.update (readRegs regs 0 1 none) 0 false) frame
        (advancedWords w)) := by
  have h1 := copy_run (sweepState regs frame w) 259 258
    (by decide) (by decide) (by decide) (by simpa [sweepState] using ht)
  have e1 : afterCopy (sweepState regs frame w) 259 258 0 1 =
      sweepState (readRegs regs 0 1 none) frame
        {w with processed := w.current ++ w.processed} := by
    simp only [afterCopy, sweepState, StackRoutines.copyStacks,
      sweepStore_current, sweepStore_processed, update_sweepStore_processed]
  rw [e1] at h1
  have h2 := clearCurrent_run (readRegs regs 0 1 none) frame
    {w with processed := w.current ++ w.processed}
  simp only [StackRoutines.readRegs_reset] at h2
  have h3 := incrementIndex_run (readRegs regs 0 1 none) frame
    (cleanedWords {w with processed := w.current ++ w.processed})
  have h := h1.seq (h2.seq h3)
  convert h using 1 <;> try rfl
  simp only [sweepState, sweepStore_current]
  omega

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
