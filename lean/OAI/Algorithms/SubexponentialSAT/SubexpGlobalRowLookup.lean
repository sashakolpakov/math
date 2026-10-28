import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowBranch
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata
import OAI.Algorithms.SubexponentialSAT.SubexpIncidenceSlotProgram
import OAI.Algorithms.SubexponentialSAT.WorkspaceCleanupProgram

namespace OAI.Algorithms

/-! Actual packing metadata and prefix-incidence calls for a global row.
The finite dispatcher distinguishes singleton, zero, and same-block cases
using these calls and real bit comparisons. -/

namespace SubexponentialSAT.SubexpGlobalRowLookup

open BitProgram StructuredCalls SubexpDenseRowTableProgram SubexpGlobalRowBranch

abbrev Metadata := Subexp.GlobalBasisMetadata.Metadata

@[simp] theorem unary_eq_iff (m n : ℕ) : unary m = unary n ↔ m = n := by
  constructor
  · intro h
    have hh := congrArg List.length h
    simpa [unary] using hh
  · rintro rfl
    rfl

theorem literalWord_eq_serialize {C : Type*} (encode : C → Word) (c : C) :
    literalWord (encode c) =
      SubexpPostfixControl.serializeCode encode (Algorithm.Expr.compile (.lit c)) := by
  simp [literalWord, Algorithm.Expr.compile, SubexpPostfixControl.serializeCode,
    SubexpPostfixControl.serializeInstr]

def firstPorts : Fin 12 → Fin 288 :=
  ![265, 260, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280]

def secondPorts : Fin 12 → Fin 288 :=
  ![265, 262, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283]

theorem firstPorts_injective : Function.Injective firstPorts := by decide
theorem secondPorts_injective : Function.Injective secondPorts := by decide

def metadata (ports : Fin 12 → Fin 288) : Code :=
  .call (ProgramLinking.liftProgram Subexp.GlobalBasisMetadata.program equalityRegisters ports)

noncomputable def metadataResult (ports : Fin 12 → Fin 288) (a : Data)
    (records : List (Word × Word)) (query : Word) (m : Metadata) : Data :=
  embedState equalityRegisters ports a
    (Subexp.GlobalBasisMetadata.outputState (Subexp.SelectorProgram.rawRecords records) query m)

/-- Actual preserving lookup and schema parsing, lifted into the row bank.
The lookup hit must be proved about the physical table that is present. -/
theorem metadata_eval (ports : Fin 12 → Fin 288) (hinj : Function.Injective ports)
    (a : Data) (records : List (Word × Word)) (query : Word) (m : Metadata)
    (hhit : records.lookup query = some m.encode)
    (hmaster : a.stacks (ports 0) = Subexp.SelectorProgram.rawRecords records)
    (hquery : a.stacks (ports 1) = query)
    (hwork : ∀ i : Fin 12, i ≠ 0 → i ≠ 1 → a.stacks (ports i) = []) :
    ∃ n ≤ 400 * (Subexp.GlobalBasisMetadata.volume records query)^2,
      Eval (metadata ports) n a (metadataResult ports a records query m) := by
  let initial := Subexp.GlobalBasisMetadata.inputState (a.regs ∘ equalityRegisters)
    (Subexp.SelectorProgram.rawRecords records) query
  have hp : projectState equalityRegisters ports a = initial := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [hmaster, hquery, hwork]
  obtain ⟨n, hn, ht⟩ := Subexp.GlobalBasisMetadata.program_runsIn records query m hhit
    (a.regs ∘ equalityRegisters)
  dsimp only [initial] at hp
  rw [← hp] at ht
  have he := eval_call_from_state Subexp.GlobalBasisMetadata.program equalityRegisters ports a
    equalityRegisters_injective hinj ht
  exact ⟨n, hn, he⟩

theorem metadataResult_flag (ports : Fin 12 → Fin 288) (a : Data)
    (records : List (Word × Word)) (query : Word) (m : Metadata) :
    (metadataResult ports a records query m).regs 4 = m.coveredFlag := by
  change (metadataResult ports a records query m).regs (equalityRegisters 4) = _
  unfold metadataResult
  rw [embedState_register _ _ _ _ equalityRegisters_injective]
  rfl

theorem metadataResult_stack (ports : Fin 12 → Fin 288) (hinj : Function.Injective ports)
    (a : Data) (records : List (Word × Word)) (query : Word) (m : Metadata) (i : Fin 12) :
    (metadataResult ports a records query m).stacks (ports i) =
      (Subexp.GlobalBasisMetadata.outputState (Subexp.SelectorProgram.rawRecords records) query m).stacks i :=
  embedState_stack _ _ _ _ hinj i

theorem metadataResult_frame (ports : Fin 12 → Fin 288) (a : Data)
    (records : List (Word × Word)) (query : Word) (m : Metadata) (i : Fin 288)
    (hi : ¬ ∃ j, ports j = i) :
    (metadataResult ports a records query m).stacks i = a.stacks i :=
  embedState_stack_frame _ _ _ _ i hi

theorem metadataResult_stacks (ports : Fin 12 → Fin 288) (hinj : Function.Injective ports)
    (a : Data) (records : List (Word × Word)) (query : Word) (m : Metadata)
    (hmaster : a.stacks (ports 0) = Subexp.SelectorProgram.rawRecords records)
    (hquery : a.stacks (ports 1) = query)
    (hwork : ∀ i : Fin 12, i ≠ 0 → i ≠ 1 → a.stacks (ports i) = []) :
    (metadataResult ports a records query m).stacks =
      Function.update (Function.update (Function.update a.stacks (ports 2) m.block)
        (ports 3) m.typeCode) (ports 4) m.rank := by
  funext i
  by_cases hi : ∃ j, ports j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [metadataResult_stack ports hinj]
    fin_cases j <;>
      simp [Subexp.GlobalBasisMetadata.outputState, hinj.eq_iff,
        hmaster, hquery, hwork]
  · have h2 : i ≠ ports 2 := fun h => hi ⟨2, h.symm⟩
    have h3 : i ≠ ports 3 := fun h => hi ⟨3, h.symm⟩
    have h4 : i ≠ ports 4 := fun h => hi ⟨4, h.symm⟩
    simpa [h2, h3, h4] using metadataResult_frame ports a records query m i hi

def slotRegisters : Fin 10 → Fin 25 := Fin.castAdd 15
def slotPorts : Fin 13 → Fin 288 :=
  ![256, 261, 260, 284, 277, 278, 279, 280, 281, 282, 283, 285, 286]

theorem slotRegisters_injective : Function.Injective slotRegisters := Fin.castAdd_injective _ _
theorem slotPorts_injective : Function.Injective slotPorts := by decide

private theorem slot_work_values (a : Data)
    (hwork : ∀ i : Fin 13, 3 ≤ i.val → a.stacks (slotPorts i) = []) :
    a.stacks 284 = [] ∧ a.stacks 277 = [] ∧ a.stacks 278 = [] ∧
      a.stacks 279 = [] ∧ a.stacks 280 = [] ∧ a.stacks 281 = [] ∧
      a.stacks 282 = [] ∧ a.stacks 283 = [] ∧ a.stacks 285 = [] ∧ a.stacks 286 = [] :=
  ⟨hwork 3 (by decide), hwork 4 (by decide), hwork 5 (by decide),
    hwork 6 (by decide), hwork 7 (by decide), hwork 8 (by decide),
    hwork 9 (by decide), hwork 10 (by decide), hwork 11 (by decide), hwork 12 (by decide)⟩

def slot : Code :=
  .call (ProgramLinking.liftProgram SubexpIncidenceSlotProgram.program slotRegisters slotPorts)

noncomputable def slotResult (a : Data) (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) : Data :=
  embedState slotRegisters slotPorts a (SubexpIncidenceSlotProgram.idle regs scopes e v
    (SubexpIncidenceSlotProgram.unary (SubexpIncidenceSlotProgram.degree scopes e v + 1)))

/-- The local slot is counted from an actually selected and scanned prefix
of the scope stream. No slot number or prefix table is supplied as input. -/
theorem slot_eval (a : Data) (scopes : List (List ℕ)) (e v : ℕ)
    (he : e ≤ scopes.length)
    (hscopes : a.stacks 256 = SubexpIncidenceSlotProgram.scopeBits scopes)
    (hfactor : a.stacks 261 = unary e) (hvertex : a.stacks 260 = unary v)
    (hwork : ∀ i : Fin 13, 3 ≤ i.val → a.stacks (slotPorts i) = []) :
    ∃ n ≤ SubexpIncidenceSlotProgram.budget scopes e v, ∃ regs,
      Eval slot n a (slotResult a regs scopes e v) := by
  obtain ⟨h284,h277,h278,h279,h280,h281,h282,h283,h285,h286⟩ := slot_work_values a hwork
  have hp : projectState slotRegisters slotPorts a =
      SubexpIncidenceSlotProgram.idle (a.regs ∘ slotRegisters) scopes e v [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        simp [slotPorts, SubexpIncidenceSlotProgram.unary,
          hscopes, hfactor, hvertex, unary, h284,h277,h278,h279,h280,h281,h282,h283,h285,h286]
  obtain ⟨regs, n, hn, ht⟩ := SubexpIncidenceSlotProgram.program_run
    (a.regs ∘ slotRegisters) scopes e v he
  rw [← hp] at ht
  exact ⟨n, hn, regs, eval_call_from_state SubexpIncidenceSlotProgram.program
    slotRegisters slotPorts a slotRegisters_injective slotPorts_injective ht⟩

theorem slotResult_stacks (a : Data) (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ)
    (hscopes : a.stacks 256 = SubexpIncidenceSlotProgram.scopeBits scopes)
    (hfactor : a.stacks 261 = unary e) (hvertex : a.stacks 260 = unary v)
    (hwork : ∀ i : Fin 13, 3 ≤ i.val → a.stacks (slotPorts i) = []) :
    (slotResult a regs scopes e v).stacks = Function.update a.stacks 284
      (unary (SubexpIncidenceSlotProgram.degree scopes e v + 1)) := by
  obtain ⟨h284,h277,h278,h279,h280,h281,h282,h283,h285,h286⟩ := slot_work_values a hwork
  funext i
  by_cases hi : ∃ j, slotPorts j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [show (slotResult a regs scopes e v).stacks (slotPorts j) =
      (SubexpIncidenceSlotProgram.idle regs scopes e v
        (SubexpIncidenceSlotProgram.unary (SubexpIncidenceSlotProgram.degree scopes e v + 1))).stacks j
      from embedState_stack _ _ _ _ slotPorts_injective j]
    fin_cases j <;>
      simp [slotPorts, SubexpIncidenceSlotProgram.idle, SubexpIncidenceSlotProgram.data,
        SubexpIncidenceSlotProgram.unary, unary, hscopes, hfactor, hvertex,
        h277,h278,h279,h280,h281,h282,h283,h285,h286]
  · have h284 : i ≠ 284 := fun h => hi ⟨3, h.symm⟩
    have hf : (slotResult a regs scopes e v).stacks i = a.stacks i :=
      embedState_stack_frame _ _ _ _ i hi
    simpa [h284] using hf

def markZero : Code := .seq (atom (.set 5 false)) (atom (.set 6 false))
def markDelta : Code := .seq (atom (.set 5 false)) (atom (.copy 6 4))
def markUniversal : Code := .seq slot (.seq (atom (.set 5 true)) (atom (.set 6 false)))

def marked (a : Data) (universal one : Bool) : Data :=
  ⟨Function.update (Function.update a.regs 5 universal) 6 one, a.stacks⟩

theorem markZero_eval (a : Data) : Eval markZero 2 a (marked a false false) := by
  let b : Data := (StructuredProgram.Atom.set 5 false).eval a
  have h1 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set 5 false) a)
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (6 : Fin 25) false)
    b)
  simpa [b, markZero, marked, atom, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h1.seq h2

theorem markDelta_eval (a : Data) : Eval markDelta 2 a (marked a false (a.regs 4)) := by
  let b : Data := (StructuredProgram.Atom.set 5 false).eval a
  have h1 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set 5 false) a)
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.copy (6 : Fin 25) 4)
    b)
  simpa [b, markDelta, marked, atom, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h1.seq h2

theorem markUniversal_eval {n : ℕ} {a b : Data} (h : Eval slot n a b) :
    Eval markUniversal (n + 2) a (marked b true false) := by
  let c : Data := (StructuredProgram.Atom.set 5 true).eval b
  have h1 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set 5 true) b)
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (6 : Fin 25) false)
    c)
  have hm : Eval (.seq (atom (.set 5 true)) (atom (.set 6 false))) 2 b (marked b true false) := by
    simpa [c, marked, atom, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h1.seq h2
  exact h.seq hm

/-- Outputs mode bits5/6. Same-block mode leaves the two actual types on
272/275 and the counted one-based slot on284. All branches are executable. -/
def classify : Code :=
  .seq (metadata firstPorts)
    (.ite 4
      (.seq (metadata secondPorts)
        (.ite 4
          (.seq (compare 271 274) (.ite 4 markUniversal markZero))
          markZero))
      (.seq (compare 260 262) markDelta))

/-- Each case below composes actual subprogram executions and charges every
tested branch. The Boolean facts come from the checked lookup/comparator. -/
theorem classify_leftover {n m : ℕ} {a b c : Data}
    (hfirst : Eval (metadata firstPorts) n a b) (hflag : b.regs 4 = false)
    (hcompare : Eval (compare 260 262) m b c) :
    Eval classify (n + (m + 2 + 1)) a (marked c false (c.regs 4)) := by
  exact hfirst.seq (Eval.ite_false hflag (hcompare.seq (markDelta_eval c)))

theorem classify_rightLeftover {n m : ℕ} {a b c : Data}
    (hfirst : Eval (metadata firstPorts) n a b) (hleft : b.regs 4 = true)
    (hsecond : Eval (metadata secondPorts) m b c) (hright : c.regs 4 = false) :
    Eval classify (n + (m + (2 + 1) + 1)) a (marked c false false) := by
  exact hfirst.seq (Eval.ite_true hleft (hsecond.seq (Eval.ite_false hright (markZero_eval c))))

theorem classify_differentBlock {n m k : ℕ} {a b c d : Data}
    (hfirst : Eval (metadata firstPorts) n a b) (hleft : b.regs 4 = true)
    (hsecond : Eval (metadata secondPorts) m b c) (hright : c.regs 4 = true)
    (hcompare : Eval (compare 271 274) k c d) (hne : d.regs 4 = false) :
    Eval classify (n + (m + ((k + (2 + 1)) + 1) + 1)) a (marked d false false) := by
  exact hfirst.seq (Eval.ite_true hleft (hsecond.seq (Eval.ite_true hright
    (hcompare.seq (Eval.ite_false hne (markZero_eval d))))))

theorem classify_sameBlock {n m k q : ℕ} {a b c d e : Data}
    (hfirst : Eval (metadata firstPorts) n a b) (hleft : b.regs 4 = true)
    (hsecond : Eval (metadata secondPorts) m b c) (hright : c.regs 4 = true)
    (hcompare : Eval (compare 271 274) k c d) (heq : d.regs 4 = true)
    (hslot : Eval slot q d e) :
    Eval classify (n + (m + ((k + ((q + 2) + 1)) + 1) + 1)) a
      (marked e true false) := by
  exact hfirst.seq (Eval.ite_true hleft (hsecond.seq (Eval.ite_true hright
    (hcompare.seq (Eval.ite_true heq (markUniversal_eval hslot))))))

/-- The chosen universal service is a fixed program, just like each constant
service. Its staging/restoration proof is a separate required dependency. -/
def source (universal : Code) : Code :=
  .seq classify (.ite 5 universal (.ite 6 (literal 132) (literal 131)))

def cleanupPorts : List (Fin 288) :=
  [271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287]

theorem cleanupPorts_nodup : cleanupPorts.Nodup := by decide

/-- Metadata and slot storage is physically cleared before source arithmetic.
The emitted code on26 and all source caches lie outside this finite list. -/
def prepare (universal : Code) : Code :=
  .seq (source universal) (WorkspaceCleanupProgram.command 0 1 cleanupPorts)

def row (universal evaluate : Code) : Code := .seq (prepare universal) evaluate

theorem prepare_execution (universal : Code) {n : ℕ} {a b : Data}
    (hsource : Eval (source universal) n a b) :
    Eval (prepare universal) (n + WorkspaceCleanupProgram.cost cleanupPorts b) a
      (WorkspaceCleanupProgram.finish 0 1 cleanupPorts b) :=
  hsource.seq (WorkspaceCleanupProgram.command_eval 0 1 cleanupPorts cleanupPorts_nodup b)

theorem row_execution (universal evaluate : Code) {n m : ℕ} {a b c : Data}
    (hsource : Eval (source universal) n a b)
    (hevaluate : Eval evaluate m (WorkspaceCleanupProgram.finish 0 1 cleanupPorts b) c) :
    Eval (row universal evaluate) (n + WorkspaceCleanupProgram.cost cleanupPorts b + m) a c :=
  (prepare_execution universal hsource).seq hevaluate

end SubexponentialSAT.SubexpGlobalRowLookup

end OAI.Algorithms
