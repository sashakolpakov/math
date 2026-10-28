import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramFrontend
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramPackLabels
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramLabels
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingCanonicalSpec

namespace OAI.Algorithms

/-! End-to-end physical packing from runtime word rows and native address
plans. Both labels and the full universal type list are generated before the
bucket/block/leftover controller runs. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.NativePacking

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

structure Spec (U : Type*) [DecidableEq U] where
  params : NativeFrontend.Params
  types : FiniteEnumeration U
  label : Fin params.D → U
  encodeType : U → List Bool
  encodeType_injective : Function.Injective encodeType
  rows_width : ∀ row ∈ params.rows, row.length = params.width.length
  plans_valid : ∀ plan ∈ params.planList, ∀ i ∈ plan, i < params.rows.length
  label_records : PackingVertexLabels.labelRecords params.rows params.planList 0 =
    BucketProgram.vertexRecords (List.finRange params.D) label encodeType
      (fun i => List.replicate i.val true)
  type_records : params.typeRows = types.values.map encodeType

def Spec.suffix {U : Type*} [DecidableEq U] (s : Spec U) : PackLabels.Spec U :=
  ⟨s.params.base,s.types,s.label,s.encodeType,s.encodeType_injective⟩

abbrev command : Cmd 16 48 := .seq (.call NativeFrontend.program) (.call PackLabels.program)
def program := compiled command 25 32

def budget {U : Type*} [DecidableEq U] (s : Spec U) : ℕ :=
  s.params.labelsBound+s.params.typesBound+PackLabels.budget s.suffix+2

theorem program_trace {U : Type*} [DecidableEq U] (s : Spec U) (regs : Fin 16 → Bool) :
    ∃ steps ≤ budget s, ∃ rf,
      Trace program steps
        ((NativeFrontend.plansState s.params regs).withPC (some program.entry))
        ((s.suffix.outputState rf).withPC none) := by
  obtain ⟨nf,hf,rf,htf⟩ := NativeFrontend.program_trace s.params regs s.rows_width s.plans_valid
  obtain ⟨ns,hs,rs,hts⟩ := PackLabels.program_trace s.suffix rf
  have hlabels : s.params.labelStream =
      BucketProgram.encodeRecords (PackLabels.records s.suffix).reverse := by
    rw [NativeFrontend.Params.labelStream,s.label_records]
    rfl
  have htypes : s.params.typeStream = ProgramEncoding.encodeRecords (PackLabels.keys s.suffix) := by
    rw [NativeFrontend.Params.typeStream,s.type_records]
    rfl
  rw [hlabels,htypes] at htf
  have e1 : Eval (.call NativeFrontend.program) nf
      (NativeFrontend.plansState s.params regs)
      (PackingProgram.frontendOutputState s.suffix.params.input
        (BucketProgram.encodeRecords (PackLabels.records s.suffix).reverse)
        (ProgramEncoding.encodeRecords (PackLabels.keys s.suffix)) rf) := .call NativeFrontend.program htf
  have e2 : Eval (.call PackLabels.program) ns
      (PackingProgram.frontendOutputState s.suffix.params.input
        (BucketProgram.encodeRecords (PackLabels.records s.suffix).reverse)
        (ProgramEncoding.encodeRecords (PackLabels.keys s.suffix)) rf)
      (s.suffix.outputState rs) := .call PackLabels.program hts
  refine ⟨nf+ns+1,?_,rs,compiled_halt_trace (e1.seq e2) 25 32⟩
  unfold budget
  omega

noncomputable def addressSpec {D r Q : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) : Spec (UniversalType r Q 1) where
  params := {
    D := D, Δ := 1, rows := words.map ReadPlan.encodeWord
    width := List.replicate (Q*r) true
    alphabet := AssignmentAlphabetSemantics.wordBytes r Q
    planList := labelPlans words address
    plans_count := by simp [labelPlans] }
  types := PackingCanonicalSpec.types hr hQ 1
  label := addressLabel words address
  encodeType := CollisionProgram.encodeType
  encodeType_injective := CollisionProgram.encodeType_injective
  rows_width := by
    intro row hrow
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hrow
    simp [ReadPlan.encodeWord_length,ReadPlan.wordWidth]
  plans_valid := labelPlans_valid words address
  label_records := addressLabel_records words address
  type_records := (PackingCanonicalSpec.types_bytes hr hQ 1).symm

/-- The sole non-scalar inputs are actual encoded words, address plans, and the
word alphabet. The latter is the same runtime alphabet used by the scorer. -/
theorem address_program_trace {D r Q : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) (regs : Fin 16 → Bool) :
    ∃ steps ≤ budget (addressSpec hr hQ words address), ∃ rf,
      Trace program steps
        ((NativeFrontend.plansState (addressSpec hr hQ words address).params regs).withPC
          (some program.entry))
        (((addressSpec hr hQ words address).suffix.outputState rf).withPC none) :=
  program_trace (addressSpec hr hQ words address) regs

end SubexponentialSAT.SqrtLog.LayoutProgram.NativePacking

end OAI.Algorithms
