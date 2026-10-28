import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStart
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramSolve

namespace OAI.Algorithms

/-! The native tail specialized to the actual sparse code, runtime alphabet,
and canonical integer mass score.  Its remaining hypotheses describe two
measured native services, rather than an additional model-equivalence oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls HashSelectProgram

theorem family_exists {n m B : ℕ} {a : Data} (hm : 0 < m)
    (ha : StartReady a n m B) :
    ∃ seed rest, generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (SparseCode.distanceDenom m B)=seed::rest := by
  have hv : CounterPrograms.value (a.stacks 768)=3*m := by
    simpa only [CounterPrograms.value_eq_toNat] using ha.count
  have hn := HashFamilyPayload.generated_nonempty hm (a.stacks 768).length
    (SparseCode.distanceDenom m B)
  rw [←HashFamilyPayload.alphabetWords_eq (a.stacks 768) hv] at hn
  cases h : generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (SparseCode.distanceDenom m B) with
  | nil => exact False.elim (hn h)
  | cons seed rest => exact ⟨seed,rest,rfl⟩

theorem solve_canonical_eval {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (hB : 0 < B) (mass acceptedCount : Cmd 40 896)
    (a : Data) (ha : StartReady a n m B)
    (s : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (hs : WalshExistence.Good (SparseCode.gapDenom m B) s)
    (hQ : SparseCode.HasDistance Q (SparseCode.degree m B/(100*B*SparseCode.logSize m)+1))
    (hrows : a.stacks 777=candidateEncoding
      (LeafScopeResourceBounds.initialPayloads (a.stacks 768).length
        (CodeRowsProgram.serializedRows m s Q)))
    (seed : List Bool) (rest : Records)
    (hfamily : generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (SparseCode.distanceDenom m B)=seed::rest)
    (cost countCost countBits : ℕ)
    (hmass : ∀ frame, Execution.Hash.ContextFrame selector a frame → ∀ rows' state,
      rows'.length < (LeafScopeResourceBounds.initialPayloads (a.stacks 768).length
        (CodeRowsProgram.serializedRows m s Q)).length+HashSelect.loopCap n m →
      rows' ⊆ (seed::rest)++LeafScopeResourceBounds.initialPayloads (a.stacks 768).length
        (CodeRowsProgram.serializedRows m s Q) →
      ControllerReady selector.controller frame (seed::rest) rows' state →
      MassSpec mass selector.controller.trial.core (afterCopyFamily selector.controller.trial state)
        (massScore clauses (a.stacks 768).length rows') (fun bits => bits ∈ seed::rest)
        (LeafParametersProgram.precision n m)
        (SparseCode.distanceDenom m B*(a.stacks 768).length) cost)
    (hcount : ∀ b : Data, Execution.Hash.ContextFrame selector a b → WorkerEmpty b →
      b.stacks 777=candidateEncoding (iter
        (payloadNext (massScore clauses (a.stacks 768).length) seed rest)
        (HashSelect.loopCap n m)
        (LeafScopeResourceBounds.initialPayloads (a.stacks 768).length
          (CodeRowsProgram.serializedRows m s Q))) →
      ∃ t ≤ countCost, ∃ c : Data, Eval acceptedCount t b c ∧ c.stacks 787=[] ∧
        (c.stacks 788).length ≤ countBits ∧
        BinaryArithmetic.toNat (c.stacks 788)=HashSelect.acceptedCount (HashSelect.cnfRowAccept clauses)
          ((iter (payloadNext (massScore clauses (a.stacks 768).length) seed rest)
            (HashSelect.loopCap n m)
            (LeafScopeResourceBounds.initialPayloads (a.stacks 768).length
              (CodeRowsProgram.serializedRows m s Q))).map
              (HashFamilyPayload.decodeVariableRow m (a.stacks 768).length))) :
    ∃ steps b bit, Eval (solve mass acceptedCount) steps a b ∧
      steps ≤ Execution.Hash.budget (a.stacks 768) (a.stacks 773) (a.stacks 774)
        (LeafParametersProgram.precision n m)
        (SparseCode.distanceDenom m B*(a.stacks 768).length) cost+
        countCost+5*countBits+11 ∧ b.stacks 787=[bit] ∧
      (bit=true ↔ ∃ x, ∀ e, (clauses e).eval x=true) := by
  have hv : CounterPrograms.value (a.stacks 768)=3*m := by
    simpa only [CounterPrograms.value_eq_toNat] using ha.count
  have hfamily' : generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (CounterPrograms.value (a.stacks 773))=seed::rest := by
    rw [CounterPrograms.value_eq_toNat,ha.depth]
    exact hfamily
  have hrounds : CounterPrograms.value (a.stacks 774)=HashSelect.loopCap n m := by
    rw [CounterPrograms.value_eq_toNat,ha.rounds]
  apply solve_eval clauses mass acceptedCount a _ (a.stacks 768).length
    (LeafParametersProgram.precision n m)
    (SparseCode.distanceDenom m B*(a.stacks 768).length) cost countCost countBits
    seed rest (massScore clauses (a.stacks 768).length) (fun _ bits => bits ∈ seed::rest)
    ha.worker ha.hash hrows hfamily'
  · simpa only [hrounds] using hmass
  · intro rows' _ _ bits hbits
    refine ⟨hbits,?_,massScore_length clauses _ _ _⟩
    have hb : bits ∈ generatedPayloads
        (HashFamilyPayload.alphabet m (a.stacks 768).length)
        (SparseCode.distanceDenom m B) := by
      rw [←HashFamilyPayload.alphabetWords_eq (a.stacks 768) hv,hfamily]
      exact hbits
    exact (HashFamilyPayload.generated_payload_width _ _ _ _ hb).le
  · simpa only [hrounds] using
      canonical_score_selected_models clauses hm hB (a.stacks 768) hv s Q hs hQ seed rest hfamily
  · simpa only [hrounds] using hcount

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
