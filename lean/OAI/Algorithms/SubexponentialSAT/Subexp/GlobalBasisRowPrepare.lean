import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisDataLookup
import OAI.Algorithms.SubexponentialSAT.SubexpHeadColorProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeFiberProgram
import OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexProgram

namespace OAI.Algorithms

/-!
# Physical row-data preparation for the global basis assembler

The persistent inputs are type index 32, packing metadata 33, vertex index
34, universal types 37, color count 38, and the current type's local-search
batch 40.  Canonical scalar frames on 13--15 are framed
by every call.  A covered row is populated by actual metadata lookup,
head-color decoding, Side filtering/rank lookup, and local-table decoding.

This module is the concrete composition layer.  The full assembler must
establish the input-table equalities from their physical producers.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisRowPrepare

open BitProgram StructuredCalls

abbrev Data := State 16 64
abbrev Code := Cmd 16 64

def smallRegs : Fin 5 → Fin 16 := Fin.castAdd 11
def metadataRegs : Fin 5 → Fin 16 := ![0, 1, 2, 3, 6]
def workRegs : Fin 8 → Fin 16 := ![0, 1, 2, 3, 4, 5, 7, 8]

theorem smallRegs_injective : Function.Injective smallRegs := Fin.castAdd_injective 5 11
theorem metadataRegs_injective : Function.Injective metadataRegs := by decide
theorem workRegs_injective : Function.Injective workRegs := by decide

def metadataPorts : Fin 12 → Fin 64 := ![33, 34, 3, 36, 5, 16, 17, 18, 19, 20, 21, 22]
def headPorts : Fin 10 → Fin 64 := ![36, 32, 38, 4, 16, 17, 18, 19, 20, 21]
def sidePorts : Fin 16 → Fin 64 :=
  ![37, 16, 17, 18, 19, 20, 21, 22, 23, 24, 41, 38, 32, 4, 43, 42]
def rankPorts : Fin 7 → Fin 64 := ![36, 41, 16, 17, 18, 19, 2]
def tablePorts : Fin 20 → Fin 64 :=
  ![40, 4, 1, 43, 0, 44, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]

theorem metadataPorts_injective : Function.Injective metadataPorts := by decide
theorem headPorts_injective : Function.Injective headPorts := by decide
theorem sidePorts_injective : Function.Injective sidePorts := by decide
theorem rankPorts_injective : Function.Injective rankPorts := by decide
theorem tablePorts_injective : Function.Injective tablePorts := by decide

def metadata : Code := .call
  (ProgramLinking.liftProgram GlobalBasisMetadata.program metadataRegs metadataPorts)
def headColor : Code := .call
  (ProgramLinking.liftProgram SubexpHeadColorProgram.program smallRegs headPorts)
def side : Code := .call
  (ProgramLinking.liftProgram (TypeFiberProgram.program false) workRegs sidePorts)
def rank : Code := liftCommand SubexpNodeIndexProgram.Internal.command 0 6 smallRegs rankPorts
def localTable : Code := .call
  (ProgramLinking.liftProgram GlobalBasisDataLookup.program workRegs tablePorts)

def clear (port : Fin 64) : Code := .call (StackRoutines.clearProgram port 0 1)

def covered : Code := .seq headColor (.seq side (.seq rank
  (.seq localTable (.seq (clear 41) (.seq (clear 43) (clear 44))))))

/-- The branch is selected by the Boolean produced by the physical metadata
parser. An uncovered row needs only its actual leftover rank. -/
def command : Code := .seq metadata
  (.seq (.ite 6 covered (.base .skip)) (clear 36))

def program := compiled command 34 0

theorem workRegs_ne_six (i : Fin 8) : workRegs i ≠ 6 := by fin_cases i <;> decide
theorem smallRegs_ne_six (i : Fin 5) : smallRegs i ≠ 6 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = 6 at hv
  omega

theorem metadata_eval (records : List (List Bool × List Bool)) (query : List Bool)
    (m : GlobalBasisMetadata.Metadata) (d : Data)
    (hfind : records.lookup query = some m.encode)
    (hi : projectState metadataRegs metadataPorts d =
      GlobalBasisMetadata.inputState (d.regs ∘ metadataRegs)
        (SelectorProgram.rawRecords records) query) :
    ∃ n e, n ≤ 400 * (GlobalBasisMetadata.volume records query)^2 ∧ Eval metadata n d e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks
        3 m.block) 36 m.typeCode) 5 m.rank ∧ e.regs 6 = m.coveredFlag := by
  obtain ⟨n, hn, he⟩ := GlobalBasisMetadata.program_runsIn records query m hfind (d.regs ∘ metadataRegs)
  rw [← hi] at he
  let b := GlobalBasisMetadata.outputState (SelectorProgram.rawRecords records) query m
  let e := embedState metadataRegs metadataPorts d b
  refine ⟨n, e, hn, eval_call_from_state _ _ _ _ metadataRegs_injective metadataPorts_injective he, ?_, ?_⟩
  · have hs : b.stacks = Function.update (Function.update (Function.update
        (GlobalBasisMetadata.inputState (d.regs ∘ metadataRegs)
          (SelectorProgram.rawRecords records) query).stacks 2 m.block) 3 m.typeCode) 4 m.rank := by
      funext i
      fin_cases i <;> simp [b, GlobalBasisMetadata.outputState,
        GlobalBasisMetadata.inputState, GlobalBasisMetadata.work]
    change Function.extend metadataPorts b.stacks d.stacks = _
    rw [hs, ← hi]
    simp only [ProgramLinking.extend_update metadataPorts_injective]
    have hp := congrArg StructuredProgram.State.stacks
      (embedState_project metadataRegs metadataPorts d metadataRegs_injective metadataPorts_injective)
    change Function.extend metadataPorts
      (projectState metadataRegs metadataPorts d).stacks d.stacks = d.stacks at hp
    rw [hp]
    rfl
  · change (embedState metadataRegs metadataPorts d b).regs (metadataRegs 4) = _
    rw [embedState_register metadataRegs metadataPorts d b metadataRegs_injective]
    rfl

/-- The head color is read from the stored one-hot type, rather than
supplied by a semantic row map. -/
theorem headColor_eval {r Q Δ : ℕ} (u : MulticolorTypes.UniversalType r Q Δ)
    (t : Fin Q) (d : Data)
    (hs : d.stacks 36 = CollisionProgram.encodeType u)
    (ht : d.stacks 32 = SubexpHeadColorProgram.unary t.val)
    (hr : d.stacks 38 = SubexpHeadColorProgram.unary r)
    (hc : SubexpHeadColorProgram.Clean (projectState smallRegs headPorts d)) :
    ∃ n e, n ≤ SubexpHeadColorProgram.budget t.val r + 1 ∧ Eval headColor n d e ∧
      e.stacks = Function.update d.stacks 4
        (SubexpHeadColorProgram.unary (u.head t).val) ∧ e.regs 6 = d.regs 6 := by
  obtain ⟨n, hn, he⟩ := SubexpHeadColorProgram.program_run u t
    (projectState smallRegs headPorts d) hs ht hr hc
  let b := SubexpHeadColorProgram.result (projectState smallRegs headPorts d) (u.head t).val
  let e := embedState smallRegs headPorts d b
  refine ⟨n, e, hn, eval_call_from_state _ _ _ _ smallRegs_injective headPorts_injective he, ?_, ?_⟩
  · change Function.extend headPorts b.stacks d.stacks = _
    change Function.extend headPorts
      (Function.update (projectState smallRegs headPorts d).stacks 3
        (SubexpHeadColorProgram.unary (u.head t).val)) d.stacks = _
    rw [ProgramLinking.extend_update headPorts_injective]
    have hp := congrArg StructuredProgram.State.stacks
      (embedState_project smallRegs headPorts d smallRegs_injective headPorts_injective)
    change Function.extend headPorts (projectState smallRegs headPorts d).stacks d.stacks = d.stacks at hp
    rw [hp]
    rfl
  · apply embedState_register_frame
    rintro ⟨i, hi⟩
    exact smallRegs_ne_six i hi

/-- The Side pass is a genuine physical filter. This local statement keeps
its input-state condition explicit for the covered-row composition. -/
theorem side_eval (ctx : TypeFiberProgram.Context) (words : List (List Bool)) (d : Data)
    (hi : projectState workRegs sidePorts d =
      TypeFiberProgram.inputState ctx words (d.regs ∘ workRegs)) :
    ∃ n e, n ≤ TypeFiberProgram.budget false ctx words ∧ Eval side n d e ∧
      e.stacks = Function.update d.stacks 41
        (ProgramEncoding.encodeRecords (TypeFiberProgram.resultWords false ctx words)) ∧
      e.regs 6 = d.regs 6 := by
  obtain ⟨rf, n, hn, he⟩ := TypeFiberProgram.program_runsIn false ctx words (d.regs ∘ workRegs)
  rw [← hi] at he
  let b := TypeFiberProgram.outputState false ctx words rf
  let e := embedState workRegs sidePorts d b
  refine ⟨n, e, hn, eval_call_from_state _ _ _ _ workRegs_injective sidePorts_injective he, ?_, ?_⟩
  · have hs : b.stacks = Function.update
        (TypeFiberProgram.inputState ctx words (d.regs ∘ workRegs)).stacks 10
        (ProgramEncoding.encodeRecords (TypeFiberProgram.resultWords false ctx words)) := by
      funext i
      by_cases hi10 : i = 10
      · subst i; simp [b, TypeFiberProgram.outputState, TypeFiberProgram.inputState, TypeFiberProgram.state]
      · simp [b, TypeFiberProgram.outputState, TypeFiberProgram.inputState,
          TypeFiberProgram.state, hi10]
    change Function.extend sidePorts b.stacks d.stacks = _
    rw [hs, ← hi, ProgramLinking.extend_update sidePorts_injective]
    have hp := congrArg StructuredProgram.State.stacks
      (embedState_project workRegs sidePorts d workRegs_injective sidePorts_injective)
    change Function.extend sidePorts (projectState workRegs sidePorts d).stacks d.stacks = d.stacks at hp
    rw [hp]
    rfl
  · apply embedState_register_frame
    rintro ⟨i, hi⟩
    exact workRegs_ne_six i hi

/-- The actual first-match index of the row type in the freshly generated
Side list becomes its local coordinate. -/
theorem rank_eval (query : List Bool) (nodes : List (List Bool)) (d : Data)
    (hi : projectState smallRegs rankPorts d =
      SubexpNodeIndexProgram.Internal.state (d.regs ∘ smallRegs) query
        (ProgramEncoding.encodeRecords nodes) [] [] [] [] []) :
    ∃ n e, n ≤ SubexpNodeIndexProgram.Internal.budget query nodes ∧ Eval rank n d e ∧
      e.stacks = Function.update d.stacks 2 (List.replicate (nodes.idxOf query) true) ∧
      e.regs 6 = d.regs 6 := by
  obtain ⟨n, hn, rf, he⟩ := SubexpNodeIndexProgram.Internal.command_eval (d.regs ∘ smallRegs) query nodes
  rw [← hi] at he
  let b := SubexpNodeIndexProgram.Internal.state rf query
    (ProgramEncoding.encodeRecords nodes) [] [] [] [] (List.replicate (nodes.idxOf query) true)
  let e := embedState smallRegs rankPorts d b
  refine ⟨n + 1, e, hn,
    eval_liftCommand_from_state _ 0 6 smallRegs rankPorts d smallRegs_injective rankPorts_injective he,
    ?_, ?_⟩
  · have hs : b.stacks = Function.update
        (SubexpNodeIndexProgram.Internal.state (d.regs ∘ smallRegs) query
          (ProgramEncoding.encodeRecords nodes) [] [] [] [] []).stacks 6
        (List.replicate (nodes.idxOf query) true) := by
      funext i
      fin_cases i <;> simp [b, SubexpNodeIndexProgram.Internal.state,
        SubexpNodeIndexProgram.Internal.store]
    change Function.extend rankPorts b.stacks d.stacks = _
    rw [hs, ← hi, ProgramLinking.extend_update rankPorts_injective]
    have hp := congrArg StructuredProgram.State.stacks
      (embedState_project smallRegs rankPorts d smallRegs_injective rankPorts_injective)
    change Function.extend rankPorts (projectState smallRegs rankPorts d).stacks d.stacks = d.stacks at hp
    rw [hp]
    rfl
  · apply embedState_register_frame
    rintro ⟨i, hi⟩
    exact smallRegs_ne_six i hi

/-- Selecting a real local-search record exposes its stored matrix and
dimensions. Only four result ports change. -/
theorem localTable_eval (before : List (List Bool)) (N split : ℕ)
    (table tail : List Bool) (d : Data)
    (h0 : d.stacks 40 = GlobalBasisRecordLookup.recordsPrefix before ++
      GlobalBasisRecordLookup.record (SubexpLocalBatchParse.payload N split table) ++ tail)
    (h1 : d.stacks 4 = GlobalBasisRecordLookup.unary before.length)
    (hc : GlobalBasisDataLookup.Clean (projectState workRegs tablePorts d)) :
    ∃ n e, n ≤ 60 * ((d.stacks 40).length + (d.stacks 4).length + 1) ∧
      Eval localTable n d e ∧
      e.stacks = Function.update (Function.update (Function.update (Function.update d.stacks
        1 (GlobalBasisRecordLookup.unary N)) 43 (GlobalBasisRecordLookup.unary split))
          0 table) 44 (GlobalBasisRecordLookup.unary (N - split)) ∧
      e.regs 6 = d.regs 6 := by
  obtain ⟨b, ⟨n, hn, he⟩, hs⟩ := GlobalBasisDataLookup.program_runsIn before N split table tail
    (projectState workRegs tablePorts d) h0 h1 hc
  let e := embedState workRegs tablePorts d b
  refine ⟨n, e, hn, eval_call_from_state _ _ _ _ workRegs_injective tablePorts_injective he, ?_, ?_⟩
  · change Function.extend tablePorts b.stacks d.stacks = _
    rw [hs]
    simp only [GlobalBasisDataLookup.resultStacks,
      ProgramLinking.extend_update tablePorts_injective]
    have hp := congrArg StructuredProgram.State.stacks
      (embedState_project workRegs tablePorts d workRegs_injective tablePorts_injective)
    change Function.extend tablePorts (projectState workRegs tablePorts d).stacks d.stacks = d.stacks at hp
    rw [hp]
    rfl
  · apply embedState_register_frame
    rintro ⟨i, hi⟩
    exact workRegs_ne_six i hi

end SubexponentialSAT.Subexp.GlobalBasisRowPrepare

end OAI.Algorithms
