import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramLookup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramOrigin
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyEncoding

namespace OAI.Algorithms

/-! Source lookup starts with the actual canonical CNF body, rather than an
externally supplied table of already expanded hash clauses. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Source
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Mapping here describes the source serialization; it is not a machine
preprocessing step. The lookup scans the supplied original bytes. -/
theorem fetch_serialized_runs {α : Type*} (clauses : List α) (enc : α → List Bool)
    (i : Fin clauses.length) (v p f : Bool) :
    ∃ flag, RunsIn fetchProgram (23*(Encoding.encodeList enc clauses).length+19)
      ((data v p f (Encoding.encodeList enc clauses) []
        (Encoding.encodeNat i.val) [] [] []).withPC (some fetchProgram.entry))
      ((data false false flag (Encoding.encodeList enc clauses) [] [] [] []
        (enc clauses[i.val])).withPC none) := by
  let j : Fin (clauses.map enc).length := ⟨i.val, by simp⟩
  have h := fetch_original_runs (clauses.map enc) j v p f
  simpa [j,ExecSparsifyEncoding.encodeList_map] using h

/-- The returned literal-code list is precisely the indexed original clause
of the canonical input, and the complete original input is preserved. -/
theorem fetch_cnf_runs {n : ℕ} (F : SAT.CNF (Fin n))
    (i : Fin (Encoding.cnfNumbers F).length) (v p f : Bool) :
    ∃ flag, RunsIn fetchProgram (23*(Encoding.encodeCNFBody F).length+19)
      ((data v p f (Encoding.encodeCNFBody F) []
        (Encoding.encodeNat i.val) [] [] []).withPC (some fetchProgram.entry))
      ((data false false flag (Encoding.encodeCNFBody F) [] [] [] []
        (Encoding.encodeList Encoding.encodeNat (Encoding.cnfNumbers F)[i.val])).withPC none) := by
  exact fetch_serialized_runs (Encoding.cnfNumbers F)
    (Encoding.encodeList Encoding.encodeNat) i v p f

/-- The same primitive accepts the exact serialized executable leaf formula.
In particular, repeated clauses and repeated literals retain their positions. -/
theorem fetch_leaf_runs {n : ℕ} (F : ExecQuantitativeSparsify.Formula n)
    (i : Fin F.length) (v p f : Bool) :
    ∃ flag, RunsIn fetchProgram
      (23*(ExecQuantitativeSparsify.encodeRawFormula F).length+19)
      ((data v p f (ExecQuantitativeSparsify.encodeRawFormula F) []
        (Encoding.encodeNat i.val) [] [] []).withPC (some fetchProgram.entry))
      ((data false false flag (ExecQuantitativeSparsify.encodeRawFormula F) [] [] [] []
        (clausePayload F[i.val])).withPC none) := by
  have h := fetch_serialized_runs F clausePayload i v p f
  have he : Encoding.encodeList clausePayload F =
      ExecQuantitativeSparsify.encodeRawFormula F := by
    rw [ExecQuantitativeSparsify.encodeRawFormula,ExecSparsifyEncoding.encodeList_map]
    congr 1
    funext ls
    exact clausePayload_codes ls
  simpa only [he] using h

end SubexponentialSAT.SqrtLog.HashInputProgram.Source

end OAI.Algorithms
