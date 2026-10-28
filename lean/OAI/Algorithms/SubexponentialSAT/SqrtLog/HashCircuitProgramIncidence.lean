import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramCanonical

namespace OAI.Algorithms

/-! The native lookup theorem specialized to actual hash-indexed incidence
payloads. Every occurrence of a variable uses the payload from the selected
hash slice; lookup correctness is discharged rather than an extra premise. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

private theorem lookup_graph {K : Type*} [DecidableEq K]
    (encode : K → List Bool) (hinj : Function.Injective encode)
    (payload : K → List Bool) (xs : List K) (k : K) (hk : k ∈ xs) :
    (xs.map fun j => (encode j,payload j)).lookup (encode k) = some (payload k) := by
  induction xs with
  | nil => simp at hk
  | cons j xs ih =>
    by_cases hj : j = k
    · subst j
      simp []
    · have he : encode j ≠ encode k := fun h => hj (hinj h)
      have hm : k ∈ xs := by simpa [hj,Ne.symm hj] using hk
      simp only [List.map_cons,List.lookup_cons]
      simp [beq_false_of_ne he.symm,ih hm]

def incidenceEntries {I : Type*} {n : ℕ}
    (payload : I → Fin n → List Bool) (i : I) : List (List Bool × List Bool) :=
  (List.finRange n).map fun v => (Encoding.encodeNat v.val,payload i v)

theorem incidenceEntries_lookup {I : Type*} {n : ℕ}
    (payload : I → Fin n → List Bool) (i : I) (v : Fin n) :
    (incidenceEntries payload i).lookup (Encoding.encodeNat v.val) = some (payload i v) := by
  apply lookup_graph (fun j : Fin n => Encoding.encodeNat j.val)
  · intro a b h
    exact Fin.ext (Encoding.encodeNat_injective h)
  · simp

/-- This is the direct original-literal input theorem, with the selected hash
index retained explicitly in the payload function and physical table. -/
theorem canonicalLiteral_incidence {I : Type*} {n : ℕ}
    (payload : I → Fin n → List Bool) (i : I) (l : SAT.Literal (Fin n))
    (regs : Fin 5 → Bool) (old : Bool) :
    ∃ regs', RunsIn canonicalLiteralProgram
      (8*l.variable.val+16 + literalFetchBudget (Encoding.encodeNat l.variable.val)
        (incidenceEntries payload i) + 9*(payload i l.variable).length+10)
      ((data regs old [] (Encoding.encodeNat (Encoding.literalCode l)).reverse []
        (Squarefree.Program.lookupRecords (incidenceEntries payload i))).withPC
          (some canonicalLiteralProgram.entry))
      ((data regs' l.positive [] [] (payload i l.variable)
        (Squarefree.Program.lookupRecords (incidenceEntries payload i))).withPC none) ∧ regs' 4 = true :=
  canonicalLiteral_runs l regs old (payload i l.variable) (incidenceEntries payload i)
    (incidenceEntries_lookup payload i l.variable)
end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
