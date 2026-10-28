import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramInitial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectScores
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram

namespace OAI.Algorithms

/-! Canonical score bytes required of the native mass callback. This is a
specification of its output, never an instruction in the finite program. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

noncomputable def massScore {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (width : ℕ) (rows : HashSelectProgram.Records) (bits : List Bool) : List Bool :=
  SubexpLiftRing.fixedBits (LeafParametersProgram.precision n m)
    (HashSelect.mass (HashSelect.cnfRowAccept clauses) (HashInput.violationWeight clauses)
      (HashFamilyPayload.decodeVariableRow m width bits ::
        rows.map (HashFamilyPayload.decodeVariableRow m width)))

theorem massScore_length {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (width : ℕ) (rows : HashSelectProgram.Records) (bits : List Bool) :
    (massScore clauses width rows bits).length=LeafParametersProgram.precision n m :=
  SubexpLiftRing.fixedBits_length _ _

theorem massScore_value {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (width : ℕ) (rows : HashSelectProgram.Records) (bits : List Bool) :
    BinaryArithmetic.toNat (massScore clauses width rows bits)=
      HashSelect.mass (HashSelect.cnfRowAccept clauses) (HashInput.violationWeight clauses)
        (HashFamilyPayload.decodeVariableRow m width bits ::
          rows.map (HashFamilyPayload.decodeVariableRow m width)) := by
  apply SubexpLiftRing.toNat_fixedBits_of_lt
  exact HashSelect.cnf_mass_lt_binary_capacity clauses _

theorem score_bytes_of_value {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (width : ℕ) (rows : HashSelectProgram.Records) (bits word : List Bool)
    (hlen : word.length=LeafParametersProgram.precision n m)
    (hval : BinaryArithmetic.toNat word=
      HashSelect.mass (HashSelect.cnfRowAccept clauses) (HashInput.violationWeight clauses)
        (HashFamilyPayload.decodeVariableRow m width bits ::
          rows.map (HashFamilyPayload.decodeVariableRow m width))) :
    word=massScore clauses width rows bits := by
  rw [←HashFamilyPayload.fixedBits_toNat word,hlen,hval]
  rfl


theorem canonical_score_selected_models {n m B : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (hm : 0 < m) (hB : 0 < B)
    (countWord : List Bool) (hcount : CounterPrograms.value countWord=3*m)
    (s : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (hs : WalshExistence.Good (SparseCode.gapDenom m B) s)
    (hQ : SparseCode.HasDistance Q (SparseCode.degree m B/(100*B*SparseCode.logSize m)+1))
    (seed : List Bool) (rest : HashSelectProgram.Records)
    (hfamily : HashSelectProgram.generatedPayloads (SubexpAlphabetProgram.alphabetWords countWord)
      (SparseCode.distanceDenom m B)=seed::rest) :
    ∀ x, HashSelect.accepts (HashSelect.cnfRowAccept clauses)
      ((HashSelectProgram.iter
        (HashSelectProgram.payloadNext (massScore clauses countWord.length) seed rest)
        (HashSelect.loopCap n m)
        (LeafScopeResourceBounds.initialPayloads countWord.length (CodeRowsProgram.serializedRows m s Q))).map
        (HashFamilyPayload.decodeVariableRow m countWord.length)) x=true ↔
      ∀ e, (clauses e).eval x=true := by
  apply initial_selected_models clauses hm hB countWord hcount s Q hs hQ seed rest hfamily
  intro t _ bits _
  exact massScore_value clauses countWord.length _ bits

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
