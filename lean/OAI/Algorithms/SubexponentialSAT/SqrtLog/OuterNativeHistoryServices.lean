import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeHistoryBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeBoundedSpec

namespace OAI.Algorithms

/-! Actual fixed native commands supply the complete outer service record.
The hypotheses here are only per-query native witnesses; all selector, frame,
source-size and accepted-output composition is proved below. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls HashSelectProgram LeafOuterProgram
open SubexpSetupStorage

 theorem family_payload_le {n m B : ℕ} (a : Data) (ha : StartReady a n m B)
    (seed : List Bool) (rest : Records)
    (hf : generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (CounterPrograms.value (a.stacks 773))=seed::rest) :
    ∀ bits∈seed::rest, bits.length ≤ CounterPrograms.value (a.stacks 773)*(a.stacks 768).length := by
  intro bits hb
  have hv : CounterPrograms.value (a.stacks 768)=3*m := by
    simpa only [CounterPrograms.value_eq_toNat] using ha.count
  apply (HashFamilyPayload.generated_payload_width m (a.stacks 768).length
    (CounterPrograms.value (a.stacks 773)) bits _).le
  rw [←HashFamilyPayload.alphabetWords_eq (a.stacks 768) hv,hf]
  exact hb

 theorem afterFamily_metadata {a frame current : Data} {family rows : Records}
    (hf : Execution.Hash.ContextFrame selector a frame)
    (hr : ControllerReady selector.controller frame family rows current) :
    (afterCopyFamily selector.controller.trial current).stacks 782=a.stacks 782 ∧
    (afterCopyFamily selector.controller.trial current).stacks 785=a.stacks 785 := by
  have h782 := hr.2.2.2.1 782 (by decide) (by decide) (by decide)
  have h785 := hr.2.2.2.1 785 (by decide) (by decide) (by decide)
  have f782 := selected_outer_frame hf 782 (by decide)
  have f785 := selected_outer_frame hf 785 (by decide)
  constructor
  · change StackRoutines.copyStacks selector.controller.trial.family
      (selector.controller.trial.core.stack 8) current.stacks 782=a.stacks 782
    rw [StackRoutines.copyStacks_frame _ _ _ _ (by decide)]
    exact h782.trans f782
  · change StackRoutines.copyStacks selector.controller.trial.family
      (selector.controller.trial.core.stack 8) current.stacks 785=a.stacks 785
    rw [StackRoutines.copyStacks_frame _ _ _ _ (by decide)]
    exact h785.trans f785

 theorem historyServices_of_native_queries {n m B : ℕ} (k : ℕ)
    (clauses : Fin m → SAT.Clause (Fin n)) (a : Data) (ha : StartReady a n m B)
    (initial : Records) (hi : a.stacks 777=candidateEncoding initial)
    (W L Q : ℕ) (hw : WordBound W a)
    (hL : W+CounterPrograms.value (a.stacks 774)*
      (2*(CounterPrograms.value (a.stacks 773)*(a.stacks 768).length)+2) ≤ L)
    (hmass : ∀ seed rest,
      generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
        (CounterPrograms.value (a.stacks 773))=seed::rest →
      ∀ frame, Execution.Hash.ContextFrame selector a frame →
      ∀ round < CounterPrograms.value (a.stacks 774), ∀ state,
      ControllerReady selector.controller frame (seed::rest)
        (iter (payloadNext (massScore clauses (a.stacks 768).length) seed rest) round initial) state →
      ∀ bits best queue regs, bits∈seed::rest → Nonempty
        (LeafOuterNative.BoundedMassWitness k (OuterQuery.massInput state regs bits best queue)
          (massScore clauses (a.stacks 768).length
            (iter (payloadNext (massScore clauses (a.stacks 768).length) seed rest) round initial) bits) L Q))
    (hcount : ∀ seed rest,
      generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
        (CounterPrograms.value (a.stacks 773))=seed::rest →
      ∀ b : Data, Execution.Hash.ContextFrame selector a b → WorkerEmpty b →
      b.stacks 777=candidateEncoding (iter
        (payloadNext (massScore clauses (a.stacks 768).length) seed rest)
        (CounterPrograms.value (a.stacks 774)) initial) →
      ∃ t out, t ≤ Q ∧ Eval (LeafProgram.Query.accepted k) t
        (projectState id workerStack (LeafOuterNative.finalStaged b)) out ∧
        BinaryArithmetic.toNat (out.stacks 323)=HashSelect.acceptedCount
          (HashSelect.cnfRowAccept clauses)
          ((iter (payloadNext (massScore clauses (a.stacks 768).length) seed rest)
            (CounterPrograms.value (a.stacks 774)) initial).map
            (HashFamilyPayload.decodeVariableRow m (a.stacks 768).length)) ∧ out.stacks 767=[]) :
    ∃ svc : HistoryServices clauses (LeafOuterNative.mass k) (LeafOuterNative.acceptedCount k) a initial,
      svc.massSteps=m*Q+LeafOuterNative.overhead L m (LeafParametersProgram.precision n m) (Q+1)+64 ∧
      svc.countSteps=5000*(L+Q+1) ∧ svc.countBits=Q+1 := by
  let M := m*Q+LeafOuterNative.overhead L m (LeafParametersProgram.precision n m) (Q+1)+64
  refine ⟨{
    massSteps := M, countSteps := 5000*(L+Q+1), countBits := Q+1,
    mass_trace := ?_, count_trace := ?_ },rfl,rfl,rfl⟩
  · intro seed rest hfamily frame hf round hround state hr
    have h := LeafOuterNative.mass_spec_bounded_sources k
      (afterCopyFamily selector.controller.trial state)
      (massScore clauses (a.stacks 768).length
        (iter (payloadNext (massScore clauses (a.stacks 768).length) seed rest) round initial))
      (fun bits => bits∈seed::rest) (LeafParametersProgram.precision n m)
      (CounterPrograms.value (a.stacks 773)*(a.stacks 768).length) L Q
      (hmass seed rest hfamily frame hf round hround state hr)
    obtain ⟨h782,h785⟩ := afterFamily_metadata hf hr
    simpa only [M,LeafOuterNative.massPrecision,h782,h785,CounterPrograms.value_eq_toNat,
      ha.clauses,ha.ambient] using h
  · intro seed rest hfamily b hf hb hr
    have hp := family_payload_le a ha seed rest hfamily
    have hs := final_sources_le hw hi hf hr hp
    have hs' : ∀ i, LeafOuterNative.AcceptedSource i → (b.stacks i).length ≤ L := by
      intro i hi
      exact (hs i hi).trans hL
    obtain ⟨t,out,ht,he,hvalue,h767⟩ := hcount seed rest hfamily b hf hb hr
    obtain ⟨v,c,hv,hc,h787,h788,_,_⟩ :=
      LeafOuterNative.accepted_bounded_of_native_sources k b L Q t hb hs' out he ht h767
    have hlen := LeafOuterNative.eval_stack_length he 323
    have hzero : (projectState id workerStack (LeafOuterNative.finalStaged b)).stacks 323=[] := by
      change (LeafOuterNative.finalStaged b).stacks 323=[]
      rw [LeafOuterNative.finalStaged_frame b 323 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hb 323
    rw [hzero,List.length_nil] at hlen
    refine ⟨v,hv,c,hc,h787,?_,?_⟩
    · rw [h788]; omega
    · rw [h788]; exact hvalue

end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
