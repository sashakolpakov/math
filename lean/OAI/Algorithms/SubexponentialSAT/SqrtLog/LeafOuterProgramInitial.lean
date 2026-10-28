import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBoundsDecode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramSupplied
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionHashCorrect

namespace OAI.Algorithms

/-! The actual serializer's payloads satisfy the initial-code hypothesis of
the actual generated-order selector. Repeated and zero raw slots are retained;
their finite-field coefficients are combined only in the semantic decoder. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open scoped BigOperators
open LeafScopeResourceBounds

theorem listCandidate_row {m : ℕ} (slots : List (Fin m × ZMod 3)) :
    HashFamily.row (listCandidate slots) = CodeRowsProgram.coefficient slots := by
  funext i
  have h := congrArg (fun xs : List (Fin m × ZMod 3) =>
    (xs.map (fun z => if z.1=i then z.2 else 0)).sum) (List.ofFn_get slots)
  change (∑ x, if (slots.get x).1 = i then (slots.get x).2 else 0) =
    (slots.map (fun z => if z.1 = i then z.2 else 0)).sum
  rw [← List.sum_ofFn]
  change (List.ofFn ((fun z => if z.1 = i then z.2 else 0) ∘ slots.get)).sum = _
  rw [← List.map_ofFn]
  exact h

theorem decode_initial_payload {m width : ℕ} (hm : 0 < m) (hwidth : 3*m ≤ 2^width)
    (slots : List (Fin m × ZMod 3)) :
    HashFamilyPayload.decodeVariableRow m width (CodeRowsProgram.rowPayload width m slots).reverse =
      CodeRowsProgram.coefficient slots := by
  rw [← listCandidate_encode,HashFamilyPayload.decodeVariableRow_encode hm hwidth,
    listCandidate_row]

theorem decode_initial_rows {m width : ℕ} (hm : 0 < m) (hwidth : 3*m ≤ 2^width)
    (rows : List (List (Fin m × ZMod 3))) :
    (initialPayloads width rows).map (HashFamilyPayload.decodeVariableRow m width) =
      rows.map CodeRowsProgram.coefficient := by
  simp only [initialPayloads,List.map_map]
  apply List.map_congr_left
  intro slots _
  exact decode_initial_payload hm hwidth slots

theorem initial_kernel_bound {m B width : ℕ} (hm : 0 < m) (hB : 0 < B)
    (hwidth : 3*m ≤ 2^width) (s : SparseCode.SuppliedShifts m B)
    (Q : SparseCode.SuppliedLocal m B) (hs : WalshExistence.Good (SparseCode.gapDenom m B) s)
    (hQ : SparseCode.HasDistance Q (SparseCode.degree m B/(100*B*SparseCode.logSize m)+1))
    (v : Fin m → ZMod 3)
    (hv : ∀ r ∈ (initialPayloads width (CodeRowsProgram.serializedRows m s Q)).map
        (HashFamilyPayload.decodeVariableRow m width), (∑ e, r e*v e)=0)
    (hv0 : v≠0) : m ≤ SparseCode.distanceDenom m B*SparseCode.weight v := by
  rw [decode_initial_rows hm hwidth] at hv
  apply CodeRowsProgram.serializedRows_kernel_bound hm hB s Q hs hQ v
  · intro row hrow
    exact hv _ (List.mem_map.mpr ⟨row,hrow,rfl⟩)
  · exact hv0

theorem initial_selected_models {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (hB : 0 < B) (countWord : List Bool)
    (hcount : CounterPrograms.value countWord=3*m)
    (s : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (hs : WalshExistence.Good (SparseCode.gapDenom m B) s)
    (hQ : SparseCode.HasDistance Q (SparseCode.degree m B/(100*B*SparseCode.logSize m)+1))
    (seed : List Bool) (rest : HashSelectProgram.Records)
    (hfamily : HashSelectProgram.generatedPayloads (SubexpAlphabetProgram.alphabetWords countWord)
      (SparseCode.distanceDenom m B)=seed::rest)
    (score : HashSelectProgram.Records → List Bool → List Bool)
    (hsound : ∀ t < HashSelect.loopCap n m, ∀ bits ∈ seed::rest,
      BinaryArithmetic.toNat (score (HashSelectProgram.iter
        (HashSelectProgram.payloadNext score seed rest) t
        (initialPayloads countWord.length (CodeRowsProgram.serializedRows m s Q))) bits) =
      HashSelect.mass (HashSelect.cnfRowAccept clauses) (HashInput.violationWeight clauses)
        (HashFamilyPayload.decodeVariableRow m countWord.length bits ::
          (HashSelectProgram.iter (HashSelectProgram.payloadNext score seed rest) t
            (initialPayloads countWord.length (CodeRowsProgram.serializedRows m s Q))).map
            (HashFamilyPayload.decodeVariableRow m countWord.length))) :
    ∀ x, HashSelect.accepts (HashSelect.cnfRowAccept clauses)
      ((HashSelectProgram.iter (HashSelectProgram.payloadNext score seed rest) (HashSelect.loopCap n m)
        (initialPayloads countWord.length (CodeRowsProgram.serializedRows m s Q))).map
        (HashFamilyPayload.decodeVariableRow m countWord.length)) x = true ↔
      ∀ e, (clauses e).eval x = true := by
  apply Execution.Hash.selected_models clauses hm countWord hcount seed rest
    (initialPayloads countWord.length (CodeRowsProgram.serializedRows m s Q)) hfamily score
  · exact initial_kernel_bound hm hB (HashFamilyPayload.countWord_width_sufficient countWord hcount).le
      s Q hs hQ
  · exact hsound

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
