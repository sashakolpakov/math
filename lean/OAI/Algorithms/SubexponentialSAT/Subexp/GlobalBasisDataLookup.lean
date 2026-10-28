import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisRecordLookup
import OAI.Algorithms.SubexponentialSAT.SubexpLocalBatchParse
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# Physical local-table lookup and decoding

This fixed command selects a color record from the current type's actual
batch and parses its three fields.  The batch and unary color index remain
intact.  The result is dimension, split, coordinate-major table, and
complement dimension; no matrix is constructed from a semantic lookup.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisDataLookup

open BitProgram StructuredCalls
open GlobalBasisRecordLookup (recordsPrefix record unary)

abbrev Data := State 8 20
abbrev Code := Cmd 8 20

def lookupPorts : Fin 8 → Fin 20 := ![0, 1, 6, 7, 8, 9, 10, 11]
theorem lookupPorts_injective : Function.Injective lookupPorts := by decide
def lookup : Code := liftCommand GlobalBasisRecordLookup.command 0 2 id lookupPorts

def Clean (d : Data) : Prop := ∀ i : Fin 20, 2 ≤ i.val → i.val ≤ 18 → d.stacks i = []

theorem lookup_eval (before : List (List Bool)) (bits tail : List Bool) (d : Data)
    (h0 : d.stacks 0 = recordsPrefix before ++ record bits ++ tail)
    (h1 : d.stacks 1 = unary before.length) (hc : Clean d) :
    ∃ e, Eval lookup (GlobalBasisRecordLookup.cost before bits tail + 1) d e ∧
      e.stacks = Function.update d.stacks 6 bits := by
  obtain ⟨b, hb, hbs⟩ := GlobalBasisRecordLookup.command_eval before bits tail
    (projectState id lookupPorts d) h0 h1
    (hc 6 (by decide) (by decide)) (hc 7 (by decide) (by decide))
    (hc 8 (by decide) (by decide)) (hc 9 (by decide) (by decide))
    (hc 10 (by decide) (by decide))
  refine ⟨embedState id lookupPorts d b,
    eval_liftCommand_from_state _ 0 2 id lookupPorts d Function.injective_id lookupPorts_injective hb, ?_⟩
  change Function.extend lookupPorts b.stacks d.stacks = _
  rw [hbs, ProgramLinking.extend_update lookupPorts_injective]
  have hp := congrArg StructuredProgram.State.stacks
    (embedState_project id lookupPorts d Function.injective_id lookupPorts_injective)
  change Function.extend lookupPorts (projectState id lookupPorts d).stacks d.stacks = d.stacks at hp
  rw [hp]
  rfl

def parsePorts : Fin 12 → Fin 20 := ![6, 2, 3, 4, 5, 12, 13, 14, 15, 16, 17, 18]
theorem parsePorts_injective : Function.Injective parsePorts := by decide
def parse : Code := liftCommand SubexpLocalBatchParse.command 0 3 id parsePorts

def resultStacks (d : Data) (N rank : ℕ) (table : List Bool) :=
  Function.update (Function.update (Function.update (Function.update d.stacks
    2 (unary N)) 3 (unary rank)) 4 table) 5 (unary (N - rank))

theorem parse_eval (N rank : ℕ) (table : List Bool) (d : Data)
    (hs : d.stacks 6 = SubexpLocalBatchParse.payload N rank table)
    (hc : ∀ i : Fin 12, i ≠ 0 → d.stacks (parsePorts i) = []) :
    ∃ e, Eval parse (SubexpLocalBatchParse.cost N rank table + 1) d e ∧
      e.stacks = resultStacks d N rank table := by
  obtain ⟨b, hb, hbs⟩ := SubexpLocalBatchParse.command_eval N rank table
    (projectState id parsePorts d) hs hc
  refine ⟨embedState id parsePorts d b,
    eval_liftCommand_from_state _ 0 3 id parsePorts d Function.injective_id parsePorts_injective hb, ?_⟩
  change Function.extend parsePorts b.stacks d.stacks = _
  rw [hbs]
  simp only [SubexpLocalBatchParse.resultStacks, ProgramLinking.extend_update parsePorts_injective]
  have hp := congrArg StructuredProgram.State.stacks
    (embedState_project id parsePorts d Function.injective_id parsePorts_injective)
  change Function.extend parsePorts (projectState id parsePorts d).stacks d.stacks = d.stacks at hp
  rw [hp]
  rfl

def clearPayload : Code := .call (StackRoutines.clearProgram 6 0 1)
def command : Code := .seq lookup (.seq parse clearPayload)
def program := compiled command 0 4

theorem command_eval (before : List (List Bool)) (N rank : ℕ) (table tail : List Bool) (d : Data)
    (h0 : d.stacks 0 = recordsPrefix before ++
      record (SubexpLocalBatchParse.payload N rank table) ++ tail)
    (h1 : d.stacks 1 = unary before.length) (hc : Clean d) :
    ∃ n e, Eval command n d e ∧
      n + 1 ≤ 60 * ((d.stacks 0).length + (d.stacks 1).length + 1) ∧
      e.stacks = resultStacks d N rank table := by
  let bits := SubexpLocalBatchParse.payload N rank table
  obtain ⟨a, ha, hsa⟩ := lookup_eval before bits tail d h0 h1 hc
  have hac : ∀ i : Fin 12, i ≠ 0 → a.stacks (parsePorts i) = [] := by
    intro i hi
    have hp6 : parsePorts i ≠ 6 := by fin_cases i <;> simp_all [parsePorts]
    have hp2 : 2 ≤ (parsePorts i).val := by fin_cases i <;> decide
    have hp18 : (parsePorts i).val ≤ 18 := by fin_cases i <;> decide
    simpa [hsa, hp6] using hc (parsePorts i) hp2 hp18
  obtain ⟨b, hb, hsb⟩ := parse_eval N rank table a (by simp [hsa, bits]) hac
  let e : Data := ⟨readRegs b.regs 0 1 none, StackRoutines.clearStacks 6 b.stacks⟩
  have hz : Eval clearPayload (2 * (b.stacks 6).length + 3) b e :=
    .call _ (ListRegisterProgram.clear_run 6 (0 : Fin 8) 1 b.regs b.stacks)
  have hb6 : b.stacks 6 = bits := by simp [hsb, resultStacks, hsa]
  refine ⟨_, e, ha.seq (hb.seq hz), ?_, ?_⟩
  · have hl := GlobalBasisRecordLookup.cost_le before bits tail
    have hp := SubexpLocalBatchParse.cost_le_payload N rank table
    have hlen : bits.length ≤ (d.stacks 0).length := by
      simp [h0, record, bits]
      omega
    rw [h0] at hlen
    rw [hb6, h0, h1]
    simp only [unary, List.length_replicate]
    dsimp only [bits] at *
    nlinarith
  · funext i
    fin_cases i <;> simp [e, StackRoutines.clearStacks, hsb, resultStacks, hsa,
      hc 6 (by decide) (by decide)]

theorem program_runsIn (before : List (List Bool)) (N rank : ℕ) (table tail : List Bool) (d : Data)
    (h0 : d.stacks 0 = recordsPrefix before ++
      record (SubexpLocalBatchParse.payload N rank table) ++ tail)
    (h1 : d.stacks 1 = unary before.length) (hc : Clean d) :
    ∃ e : Data, RunsIn program (60 * ((d.stacks 0).length + (d.stacks 1).length + 1))
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = resultStacks d N rank table := by
  obtain ⟨n, e, he, hn, hs⟩ := command_eval before N rank table tail d h0 h1 hc
  exact ⟨e, ⟨n + 1, hn, compiled_halt_trace he 0 4⟩, hs⟩

end SubexponentialSAT.Subexp.GlobalBasisDataLookup

end OAI.Algorithms
