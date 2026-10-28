import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyOuter
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramIncidence

namespace OAI.Algorithms

/-! The native descending/prepending loop produces the exact raw incidence
slice consumed by the original-variable literal lookup. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

theorem tableResult_incidence (payload : ℕ → List Bool) (n : ℕ) :
    tableResult payload n []=Squarefree.Program.lookupRecords
      (HashCircuitProgram.incidenceEntries (fun (_ : Unit) (v : Fin n) => payload v.val) ()) := by
  rw [tableResult_eq]
  simp only [List.append_nil,HashCircuitProgram.incidenceEntries,
    Squarefree.Program.lookupRecords,Subexp.SelectorProgram.rawRecords,List.flatMap_map]
  rw [← List.map_coe_finRange n,List.flatMap_map]
  rfl

/-- Every original-variable query hits the emitted payload, including high
variables, whose payload is the native current-branch constant dictionary. -/
theorem table_entries_lookup (payload : ℕ → List Bool) (n : ℕ) (v : Fin n) :
    (HashCircuitProgram.incidenceEntries (fun (_ : Unit) (w : Fin n) => payload w.val) ()).lookup
      (Encoding.encodeNat v.val)=some (payload v.val) :=
  HashCircuitProgram.incidenceEntries_lookup _ () v

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
