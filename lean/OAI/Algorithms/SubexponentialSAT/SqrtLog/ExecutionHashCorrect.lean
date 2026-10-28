import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionHash
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyPayloadSelect

namespace OAI.Algorithms

/-! Correctness of the actual payload order produced by the runtime tuple
generator. Initial rows use the variable-length decoder too. Exact score
values below are obligations of the paid mass service, not a computational
definition used as one machine instruction. -/

namespace SubexponentialSAT.SqrtLog.Execution.Hash

open HashSelectProgram HashSelect
open scoped BigOperators

theorem selected_mass_zero {n m depth : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (countWord : List Bool) (hcountWord : CounterPrograms.value countWord = 3*m)
    (seed : List Bool) (rest initial : Records)
    (hfamily : generatedPayloads (SubexpAlphabetProgram.alphabetWords countWord) depth = seed :: rest)
    (score : Records → List Bool → List Bool)
    (hcode : ∀ v : Row m,
      (∀ r ∈ initial.map (HashFamilyPayload.decodeVariableRow m countWord.length),
        (∑ e, r e * v e) = 0) → v ≠ 0 → m ≤ depth * SparseCode.weight v)
    (hsound : ∀ t < loopCap n m, ∀ bits ∈ seed :: rest,
      BinaryArithmetic.toNat (score (iter (payloadNext score seed rest) t initial) bits) =
        mass (cnfRowAccept clauses) (HashInput.violationWeight clauses)
          (HashFamilyPayload.decodeVariableRow m countWord.length bits ::
            (iter (payloadNext score seed rest) t initial).map
              (HashFamilyPayload.decodeVariableRow m countWord.length))) :
    mass (cnfRowAccept clauses) (HashInput.violationWeight clauses)
      ((iter (payloadNext score seed rest) (loopCap n m) initial).map
        (HashFamilyPayload.decodeVariableRow m countWord.length)) = 0 := by
  let decode := HashFamilyPayload.decodeVariableRow m countWord.length
  let evaluate := mass (cnfRowAccept clauses) (HashInput.violationWeight clauses)
  let c := (3*m)^depth-1
  have hpos : 0 < (3*m)^depth := pow_pos (by omega) _
  have hc : (3*m)^depth = c+1 := by dsimp [c]; omega
  have hw : 3*m ≤ 2^countWord.length :=
    (HashFamilyPayload.countWord_width_sufficient countWord hcountWord).le
  have hf : generatedPayloads (HashFamilyPayload.alphabet m countWord.length) depth = seed :: rest := by
    simpa only [HashFamilyPayload.alphabetWords_eq countWord hcountWord] using hfamily
  have cover := HashFamilyPayload.list_variable_tupleFamily_coverage hm hc
    countWord.length hw seed rest hf
  have hz : mass (cnfRowAccept clauses) (HashInput.violationWeight clauses)
      (listRun evaluate decode seed rest (initial.map decode) (loopCap n m)) = 0 := by
    apply listRun_zero (cnfRowAccept clauses) (HashInput.violationWeight clauses)
      evaluate decode seed rest (tupleFamily hc) (initial.map decode) n m
    · simp [SAT.Assignment]
    · intro x
      simpa using HashInput.violationWeight_le clauses x
    · exact cover
    · intros; rfl
    · exact initial_coverage_of_code clauses hm hc (initial.map decode) hcode
  rw [decoded_result evaluate decode score seed rest initial (loopCap n m) hsound]
  exact hz

/-- The selected rows characterize the original Boolean models. An actual
SAT answer still requires the separate paid accepted-count query. -/
theorem selected_models {n m depth : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m)
    (countWord : List Bool) (hcountWord : CounterPrograms.value countWord = 3*m)
    (seed : List Bool) (rest initial : Records)
    (hfamily : generatedPayloads (SubexpAlphabetProgram.alphabetWords countWord) depth = seed :: rest)
    (score : Records → List Bool → List Bool)
    (hcode : ∀ v : Row m,
      (∀ r ∈ initial.map (HashFamilyPayload.decodeVariableRow m countWord.length),
        (∑ e, r e * v e) = 0) → v ≠ 0 → m ≤ depth * SparseCode.weight v)
    (hsound : ∀ t < loopCap n m, ∀ bits ∈ seed :: rest,
      BinaryArithmetic.toNat (score (iter (payloadNext score seed rest) t initial) bits) =
        mass (cnfRowAccept clauses) (HashInput.violationWeight clauses)
          (HashFamilyPayload.decodeVariableRow m countWord.length bits ::
            (iter (payloadNext score seed rest) t initial).map
              (HashFamilyPayload.decodeVariableRow m countWord.length))) :
    ∀ x, accepts (cnfRowAccept clauses)
      ((iter (payloadNext score seed rest) (loopCap n m) initial).map
        (HashFamilyPayload.decodeVariableRow m countWord.length)) x = true ↔
      ∀ e, (clauses e).eval x = true :=
  cnf_mass_zero_iff clauses _
    (selected_mass_zero clauses hm countWord hcountWord seed rest initial hfamily score hcode hsound)

end SubexponentialSAT.SqrtLog.Execution.Hash

end OAI.Algorithms
