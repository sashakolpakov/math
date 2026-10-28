import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramControl

namespace OAI.Algorithms

/-! Direct-call interface from the actual caller state. This avoids preparing
an extra machine-state embedding between the record parser and literal lookup. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem fetchLiteral_from_state (d : Machine) (regs : Fin 5 → Bool) (old positive : Bool)
    (v : ℕ) (payload : List Bool) (entries : List (List Bool × List Bool))
    (hlookup : entries.lookup (Encoding.encodeNat v) = some payload)
    (hports : projectState literalRegisters literalStacks d =
      data regs old [] (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse []
        (Squarefree.Program.lookupRecords entries)) :
    ∃ n ≤ 8*v+16 + literalFetchBudget (Encoding.encodeNat v) entries + 9*payload.length+10,
      ∃ regs', Eval fetchLiteral n d
        (literalFrame d regs' positive [] [] payload (Squarefree.Program.lookupRecords entries)) ∧
        regs' 4 = true := by
  obtain ⟨n,hn,rr,he,hf⟩ := canonicalLiteral_hit regs old positive v payload entries hlookup
  rw [← hports] at he
  exact ⟨n+1,by omega,rr,
    eval_liftCommand_from_state canonicalLiteral 2 5 literalRegisters literalStacks d
      literalRegisters_injective literalStacks_injective he,hf⟩

/-- The unread literal-list tail is preserved by the complete lookup call. -/
theorem fetched_clause_tail (d : Machine) (regs : Fin 5 → Bool) (positive : Bool)
    (payload table : List Bool) :
    (literalFrame d regs positive [] [] payload table).stacks 63 = d.stacks 63 :=
  literalFrame_stack d regs positive [] [] payload table 63 (Or.inr (by decide))

/-- The unread weighted-row tail is also preserved while a literal is fetched. -/
theorem fetched_row_tail (d : Machine) (regs : Fin 5 → Bool) (positive : Bool)
    (payload table : List Bool) :
    (literalFrame d regs positive [] [] payload table).stacks 64 = d.stacks 64 :=
  literalFrame_stack d regs positive [] [] payload table 64 (Or.inr (by decide))

def callerRegs (d : Machine) : Fin 5 → Bool := fun i => d.regs (Fin.castAdd 3 i)

structure LookupReady (d : Machine) (table : List Bool) : Prop where
  scan : d.stacks 56 = []
  temporary : d.stacks 57 = []
  compare : d.stacks 59 = []
  scratch : d.stacks 60 = []
  output : d.stacks 61 = []
  saved : d.stacks 62 = table

theorem project_lookup (d : Machine) (query table : List Bool)
    (h : LookupReady d table) (hq : d.stacks 58 = query) :
    projectState literalRegisters literalStacks d = data (callerRegs d) (d.regs 5) [] query [] table := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i
    · exact h.scan
    · exact h.temporary
    · exact hq
    · exact h.compare
    · exact h.scratch
    · exact h.output
    · exact h.saved

theorem lookupReady_recordState (d : Machine) (table source payload : List Bool)
    (h : LookupReady d table) (v pr f : Bool) :
    LookupReady (RecordPrograms.state literalPorts d v pr f source payload) table := by
  constructor <;>
    simp [RecordPrograms.state,literalPorts,h.scan,h.temporary,h.compare,h.scratch,h.output,h.saved]

def parsed (d : Machine) (code : ℕ) (tail : List Bool) : Machine :=
  RecordPrograms.state literalPorts d false true false tail (Encoding.encodeNat code).reverse

abbrev parseAndFetch : Cmd 8 96 := .seq (RecordPrograms.reader literalPorts) fetchLiteral

/-- One complete physical literal read: framed original literal code to raw
incidence dictionary, including both parser and lookup costs. -/
theorem parseAndFetch_eval {n : ℕ} (d : Machine) (l : SAT.Literal (Fin n))
    (entries : List (List Bool × List Bool)) (payload tail : List Bool)
    (hready : LookupReady d (Squarefree.Program.lookupRecords entries))
    (hlookup : entries.lookup (Encoding.encodeNat l.variable.val) = some payload)
    (v pr : Bool) :
    ∃ cost ≤ 6*(Encoding.encodeNat (Encoding.literalCode l)).length +
      8*l.variable.val+16 + literalFetchBudget (Encoding.encodeNat l.variable.val) entries +
      9*payload.length+14, ∃ rr,
      Eval parseAndFetch cost
        (RecordPrograms.state literalPorts d v pr false
          (Encoding.frame (Encoding.encodeNat (Encoding.literalCode l)) ++ tail) [])
        (literalFrame (parsed d (Encoding.literalCode l) tail) rr l.positive [] [] payload
          (Squarefree.Program.lookupRecords entries)) := by
  let mid := parsed d (Encoding.literalCode l) tail
  have hr := RecordPrograms.reader_eval literalPorts d
    (Encoding.encodeNat (Encoding.literalCode l)) tail [] v pr false
  simp only [List.append_nil] at hr
  have hm : LookupReady mid (Squarefree.Program.lookupRecords entries) :=
    lookupReady_recordState d _ _ _ hready false true false
  have hq : mid.stacks 58 = (Encoding.encodeNat (Encoding.literalCode l)).reverse := by
    exact RecordPrograms.state_payload literalPorts d false true false tail _
  have hp := project_lookup mid _ _ hm hq
  obtain ⟨c,hc,rr,he,hf⟩ := fetchLiteral_from_state mid (callerRegs mid) (mid.regs 5)
    l.positive l.variable.val payload entries hlookup hp
  refine ⟨6*(Encoding.encodeNat (Encoding.literalCode l)).length+4+c,by omega,rr,?_⟩
  exact hr.seq he

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
