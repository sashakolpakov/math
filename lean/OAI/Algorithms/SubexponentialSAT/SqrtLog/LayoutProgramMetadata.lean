import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramPackLabels
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata

namespace OAI.Algorithms

/-! Paid access to the metadata produced by the actual label-packing suffix.
The query is an incidence position, not an original variable address. The
owner-fiber scan is responsible for selecting those positions. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram

variable {U : Type*} [DecidableEq U]

def metadataValue (s : Spec U) (v : Fin s.params.D) : GlobalBasisMetadata.Metadata :=
  PackingMetadata.value s.packing s.encodeType v

/-- Lookup preserves the actual metadata table and query, returns block/type
or leftover rank, and clears every temporary stack. -/
theorem metadata_program_runsIn (s : Spec U) (v : Fin s.params.D)
    (regs : GlobalBasisMetadata.Regs) :
    RunsIn GlobalBasisMetadata.program
      (400*(s.metadata.length+v.val+1)^2)
      ((GlobalBasisMetadata.inputState regs s.metadata (s.encodeVertex v)).withPC
        (some GlobalBasisMetadata.program.entry))
      ((GlobalBasisMetadata.outputState s.metadata (s.encodeVertex v) (metadataValue s v)).withPC none) := by
  have h := GlobalBasisMetadata.program_runsIn
    (PackingMetadata.records s.packing s.encodeVertex s.encodeType) (s.encodeVertex v)
    (metadataValue s v)
    (PackingMetadata.lookup_eq s.packing s.encodeVertex s.encodeType s.encodeVertex_injective v) regs
  simpa [Spec.metadata,GlobalBasisMetadata.volume,Spec.encodeVertex] using h

theorem metadata_covered_iff (s : Spec U) (v : Fin s.params.D)
    (j : Fin s.packing.blockCount) (u : U) :
    metadataValue s v = .covered (List.replicate j.val true) (s.encodeType u) ↔
      s.packing.lookup v = some (j,u) :=
  PackingMetadata.value_eq_covered_iff s.packing s.encodeType s.encodeType_injective v j u

theorem metadata_uncovered (s : Spec U) (v : Fin s.params.D)
    (hv : s.packing.lookup v = none) :
    metadataValue s v = .leftover (List.replicate (s.packing.leftovers.idxOf v) true) := by
  simp [metadataValue,PackingMetadata.value,hv,PackingMetadata.unary]

end SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

end OAI.Algorithms
