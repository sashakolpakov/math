import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramCanonical

namespace OAI.Algorithms

/-! Exact remaining native-service interface.  Both commands are fixed
instruction tables; this record contains their measured traces and meaning.
It does not add an operation to either machine. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls HashSelectProgram

structure NativeServices {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (mass acceptedCount : Cmd 40 896) (a : Data) (initial : Records) where
  massSteps : ℕ
  countSteps : ℕ
  countBits : ℕ
  mass_trace : ∀ seed rest,
    generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (CounterPrograms.value (a.stacks 773))=seed::rest →
    ∀ frame, Execution.Hash.ContextFrame selector a frame → ∀ rows' state,
      rows'.length < initial.length+CounterPrograms.value (a.stacks 774) →
      rows' ⊆ (seed::rest)++initial →
      ControllerReady selector.controller frame (seed::rest) rows' state →
      MassSpec mass selector.controller.trial.core (afterCopyFamily selector.controller.trial state)
        (massScore clauses (a.stacks 768).length rows') (fun bits => bits ∈ seed::rest)
        (LeafParametersProgram.precision n m)
        (CounterPrograms.value (a.stacks 773)*(a.stacks 768).length) massSteps
  count_trace : ∀ seed rest,
    generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (CounterPrograms.value (a.stacks 773))=seed::rest →
    ∀ b : Data, Execution.Hash.ContextFrame selector a b → WorkerEmpty b →
      b.stacks 777=candidateEncoding (iter
        (payloadNext (massScore clauses (a.stacks 768).length) seed rest)
        (CounterPrograms.value (a.stacks 774)) initial) →
      ∃ t ≤ countSteps, ∃ c : Data, Eval acceptedCount t b c ∧ c.stacks 787=[] ∧
        (c.stacks 788).length ≤ countBits ∧
        BinaryArithmetic.toNat (c.stacks 788)=HashSelect.acceptedCount (HashSelect.cnfRowAccept clauses)
          ((iter (payloadNext (massScore clauses (a.stacks 768).length) seed rest)
            (CounterPrograms.value (a.stacks 774)) initial).map
              (HashFamilyPayload.decodeVariableRow m (a.stacks 768).length))

abbrev NativeServices.budget {n m : ℕ} {clauses : Fin m → SAT.Clause (Fin n)}
    {mass acceptedCount : Cmd 40 896} {a : Data} {initial : Records}
    (svc : NativeServices clauses mass acceptedCount a initial) : ℕ :=
  Execution.Hash.budget (a.stacks 768) (a.stacks 773) (a.stacks 774)
    (LeafParametersProgram.precision n m)
    (CounterPrograms.value (a.stacks 773)*(a.stacks 768).length) svc.massSteps+
      svc.countSteps+5*svc.countBits+11

theorem NativeServices.run {n m B : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (hB : 0 < B) (mass acceptedCount : Cmd 40 896)
    (a : Data) (ha : StartReady a n m B)
    (s : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (hs : WalshExistence.Good (SparseCode.gapDenom m B) s)
    (hQ : SparseCode.HasDistance Q (SparseCode.degree m B/(100*B*SparseCode.logSize m)+1))
    (hrows : a.stacks 777=candidateEncoding
      (LeafScopeResourceBounds.initialPayloads (a.stacks 768).length
        (CodeRowsProgram.serializedRows m s Q)))
    (svc : NativeServices clauses mass acceptedCount a
      (LeafScopeResourceBounds.initialPayloads (a.stacks 768).length
        (CodeRowsProgram.serializedRows m s Q))) :
    ∃ steps b bit, Eval (solve mass acceptedCount) steps a b ∧
      steps ≤ svc.budget ∧ b.stacks 787=[bit] ∧
      (bit=true ↔ ∃ x, ∀ e, (clauses e).eval x=true) := by
  obtain ⟨seed,rest,hfamily⟩ := family_exists hm ha
  have hd : CounterPrograms.value (a.stacks 773)=SparseCode.distanceDenom m B := by
    simpa only [CounterPrograms.value_eq_toNat] using ha.depth
  have hk : CounterPrograms.value (a.stacks 774)=HashSelect.loopCap n m := by
    simpa only [CounterPrograms.value_eq_toNat] using ha.rounds
  have hf : generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (CounterPrograms.value (a.stacks 773))=seed::rest := by
    simpa only [hd] using hfamily
  have hmass := svc.mass_trace seed rest hf
  have hcount := svc.count_trace seed rest hf
  obtain ⟨steps,b,bit,he,hcost,hbit,hsat⟩ := solve_canonical_eval clauses hm hB
    mass acceptedCount a ha s Q hs hQ hrows seed rest hfamily
    svc.massSteps svc.countSteps svc.countBits
    (by simpa only [hd,hk] using hmass) (by simpa only [hk] using hcount)
  exact ⟨steps,b,bit,he,by simpa only [NativeServices.budget,hd] using hcost,hbit,hsat⟩

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
