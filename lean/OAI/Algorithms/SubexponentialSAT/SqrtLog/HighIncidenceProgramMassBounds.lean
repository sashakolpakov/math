import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramMass
import OAI.Algorithms.SubexponentialSAT.SubexpIncidenceSlotProgram

namespace OAI.Algorithms

/-! Serialized scope adapter and complete bit cost for the nested counter.
The counter counts supplied entries; the caller's normalization invariant is
what identifies this with distinct factor-variable incidence mass. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def scopeRecords (scopes : List (List ℕ)) : List (List (List Bool)) :=
  scopes.map (List.map Encoding.encodeNat)

theorem encode_map_nat (xs : List ℕ) :
    encode (xs.map Encoding.encodeNat) = Encoding.encodeList Encoding.encodeNat xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, encode, Encoding.encodeList, id_eq, ih]

theorem encoded_scopeRecords (scopes : List (List ℕ)) :
    encode ((scopeRecords scopes).map encode) = SubexpIncidenceSlotProgram.scopeBits scopes := by
  induction scopes with
  | nil => rfl
  | cons xs xss ih =>
      simpa only [scopeRecords, List.map_cons, encode, Encoding.encodeList,
        id_eq, encode_map_nat, SubexpIncidenceSlotProgram.scopeBits,
        SubexpIncidenceSlotProgram.scopeBytes, SubexpIncidencePlanScan.scopeBytes] using
        congrArg (fun tail => true :: (Encoding.frame
          (Encoding.encodeList Encoding.encodeNat xs) ++ tail)) ih

theorem scopeRecords_mass (scopes : List (List ℕ)) :
    ((scopeRecords scopes).map List.length).sum = (scopes.map List.length).sum := by
  simp [scopeRecords, List.map_map, Function.comp_def]

theorem budget_le_input (records : List (List (List Bool))) :
    4 + RecordPrograms.budget (fun bits => 6 * bits.length + 5) (records.map encode) ≤
      28 * ((encode (records.map encode)).length + 1) := by
  exact RecordPrograms.program_budget_le_input _ _ 6 5 (by intros; rfl)

/-- The supplied nested Nat scopes are scanned, including every empty scope.
No externally supplied mass occurs in either the program or its input. -/
theorem scopes_runsIn (regs : Fin 5 → Bool) (scopes : List (List ℕ)) :
    ∃ rf, RunsIn program
      (28 * ((SubexpIncidenceSlotProgram.scopeBits scopes).length + 1))
      ((RecordPrograms.state ports (state regs [] [] [] []) false true false
        (SubexpIncidenceSlotProgram.scopeBits scopes) []).withPC (some program.entry))
      ((state rf [] [] (List.replicate ((scopes.map List.length).sum) true) []).withPC none) := by
  obtain ⟨rf, hr⟩ := program_runsIn regs (scopeRecords scopes)
  refine ⟨rf, ?_⟩
  have hb := budget_le_input (scopeRecords scopes)
  simpa only [encoded_scopeRecords, scopeRecords_mass] using hr.mono hb

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass

end OAI.Algorithms
