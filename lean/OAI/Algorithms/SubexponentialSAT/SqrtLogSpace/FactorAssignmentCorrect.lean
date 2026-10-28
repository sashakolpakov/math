import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary

/-! The actual initializer, source-context cache, dispatcher, specialized
incidence producer and factor arithmetic instantiate the stored-ID fold.
The output is the entire specialized coefficient-ring product on stack854.
Every resource assertion below concerns this same fixed command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect

open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram MomentsProgram
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram FactorAssignmentBoundary FactorAssignmentLoop

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q n d P M S : ℕ} {q : Factor.Spec r Q n d}

def assignmentBudget (q : Factor.Spec r Q n d) (P S Z : ℕ) : ℕ :=
  entryScratch.length * (2 * P + 3) + 1100 * (P + 1) + 2 +
    uniformProductBudget n (baseWidth 3 q.p.t) d q.u q.J P
      (FactorAssignmentCallback.uniformCallbackBudget q P S Z)

/-- The whole accepted-assignment budget is a fixed fourth power of the
explicit callback budget and structural dimensions. Composing the callback's
fixed polynomial keeps the exponent independent of the input. -/
theorem assignmentBudget_polynomial (q : Factor.Spec r Q n d) (P S Z : ℕ) :
    assignmentBudget q P S Z ≤
      1600 * (entryScratch.length + n + baseWidth 3 q.p.t + d + q.u + q.J + P +
        FactorAssignmentCallback.uniformCallbackBudget q P S Z + 1)^4 := by
  let C := FactorAssignmentCallback.uniformCallbackBudget q P S Z
  let X := entryScratch.length + n + baseWidth 3 q.p.t + d + q.u + q.J + P + C + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have he : entryScratch.length ≤ X := by dsimp [X]; omega
  have hp : P ≤ X := by dsimp [X]; omega
  have hp1 : P+1 ≤ X := by dsimp [X]; omega
  have hb := uniformProductBudget_polynomial n (baseWidth 3 q.p.t) d q.u q.J P C
  have hc : entryScratch.length*(2*P+3) ≤ 5*X^2 := by
    have h : entryScratch.length*(2*P+3) ≤ X*(2*X+3) := by gcongr
    nlinarith
  have hy : n+baseWidth 3 q.p.t+d+q.u+q.J+P+C+1 ≤ X := by dsimp [X]; omega
  have hh : uniformProductBudget n (baseWidth 3 q.p.t) d q.u q.J P C ≤ 256*X^4 := by
    apply hb.trans
    gcongr
  have h1 : X ≤ X^4 := by simpa using Nat.pow_le_pow_right hX (show 1 ≤ 4 by decide)
  have h2 : X^2 ≤ X^4 := Nat.pow_le_pow_right hX (by decide)
  have h0 : 1 ≤ X^4 := Nat.one_le_pow _ _ hX
  change entryScratch.length*(2*P+3)+1100*(P+1)+2+
    uniformProductBudget n (baseWidth 3 q.p.t) d q.u q.J P C ≤ 1600*X^4
  omega

/-- Multiplication occurs with one shared correction assignment throughout.
Only after the entire group product may an additive coefficient readout be
applied. The identity includes an empty group. -/
theorem specialized_product (s : Fin 768 → List Bool) (U : Fin n → Bool)
    (ids : List ℕ) :
    (ids.map (fun f => QueryEvaluation.specializeDense q.u q.J U (q.value s f))).prod =
      QueryEvaluation.specializeDense q.u q.J U
        (Squarefree.canonical q.u q.J ((ids.map (q.value s)).prod)) := by
  rw [QueryJetSemantics.specializeDense_canonical, map_list_prod, List.map_map]
  rfl

/-- The reassociation is between the two actual syntax trees, with the
same initializer and setup executions. -/
theorem prepare_product_eval {a b c : FactorAssignmentProgram.Data} {k l : ℕ}
    (hp : Eval FactorAssignmentBoundary.prepare k a b) (hq : Eval product l b c) :
    Eval assignment (k + l) a c := by
  unfold FactorAssignmentBoundary.prepare at hp
  cases hp with
  | seq hi hs =>
    simpa only [assignment, Nat.add_assoc] using hi.seq (hs.seq hq)

/-- Initialization and cache rebuilding preserve all unallocated caller
storage. This includes the representative baseline, correction mask and head
sum, without a premise about their contents. -/
theorem prepare_stack_frame {a b : FactorAssignmentProgram.Data} {k : ℕ}
    (he : Eval FactorAssignmentBoundary.prepare k a b) (i : Fin 896)
    (hi : i ∉ entryScratch) (hc : i ∉ cachePorts.map lowStack) :
    b.stacks i = a.stacks i := by
  obtain ⟨z,hz,hlo,hhi⟩ := setup_eval (initialized a)
  have hzb : z = b := Eval.final_unique 0 ((initialize_eval a).seq hz) he
  rw [← hzb]
  by_cases hlt : i.val < 768
  · let j : Fin 768 := ⟨i.val,hlt⟩
    have hj : lowStack j = i := Fin.ext rfl
    have hn : j ∉ cachePorts := by
      intro hm
      exact hc (List.mem_map.mpr ⟨j,hm,hj⟩)
    rw [← hj,hlo j,setup_local_frame _ j hn]
    change (initialized a).stacks (lowStack j) = _
    rw [hj, initialized_stacks, ite_eq_right hi]
  · rw [hhi i (by omega), initialized_stacks, ite_eq_right hi]

/-- The prepared machine runs the concrete factor callback for every stored
ID. Neutral IDs and the empty list retain the actual stored identity. -/
theorem prepared_product_eval_correct
    {a : FactorAssignmentProgram.Data}
    {one : Raw n (baseWidth 3 q.p.t) d}
    (h : Ready q P S one a) (ids : List ℕ)
    (hone : NativeSemantics.Good ∅ q.u q.J one)
    (honeval : TruncatedRingProgram.rawDenote q.p.ops.decode one =
      Squarefree.canonical q.u q.J 1)
    (honedense : TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode one = 1)
    (hids : a.stacks 175 = ProgramEncoding.encodeRecords (records ids))
    (hblank : ∀ i ∈ ([149,150,151,159,854] : List (Fin 896)), a.stacks i = [])
    (width Z : ℕ)
    (hwidth : ∀ f (hf : f < q.rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length ≤ width)
    (hZ : 1 ≤ Z) (hP : P ≤ Z) (hbit : q.bitWidth ≤ Z)
    (hshape : d * baseWidth 3 q.p.t ≤ Z)
    (hhashScale : ∀ f (hf : f < q.rows.length),
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length ≤ Z)
    (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0 ≤ Z) :
    ∃ (out : Raw n (baseWidth 3 q.p.t) d) (steps : ℕ) (b : FactorAssignmentProgram.Data), NativeSemantics.Good ∅ q.u q.J out ∧
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode out =
        (ids.map (fun f => QueryEvaluation.specializeDense q.u q.J
          (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
          (q.value (a.stacks ∘ lowStack) f))).prod ∧
      steps ≤ uniformProductBudget n (baseWidth 3 q.p.t) d q.u q.J P
        (FactorAssignmentCallback.uniformCallbackBudget q P S Z) ∧
      Eval product steps a b ∧
      b.stacks = Function.update a.stacks 854 (Product.bytes out) ∧
      WordBound P b := by
  let value := fun f => QueryEvaluation.specializeDense q.u q.J
    (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
    (q.value (a.stacks ∘ lowStack) f)
  let decode := TruncatedRingProgram.rawValue (n := n) q.u q.J q.p.ops.decode
  let step := fun seed f out => decode out = decode seed * value f
  have hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ P := by
    rw [← hids]
    exact h.incoming 175
  have hidLength (f : ℕ) (hf : f ∈ ids) : f + 1 ≤ P := by
    have hb := HashInputProgram.Loop.original_payload_length_le (records ids)
      (Encoding.encodeNat f) (List.mem_map.mpr ⟨f,hf,rfl⟩)
    simpa only [Encoding.length_encodeNat] using hb.trans hlen
  obtain ⟨out,hout,hfold,k,hk,rr,he⟩ := product_eval q.u q.J step
    (fun base => base = a.stacks) (fun f => f ∈ ids) P
    (FactorAssignmentCallback.uniformCallbackBudget q P S Z)
    (by
      intro base hb f seed tail regs hf hseed htail
      subst base
      exact h.callback_eval hone honeval regs seed tail f width Z hseed htail
        (hidLength f hf) (hwidth f) hZ hP hbit hshape (hhashScale f) hmarkScale)
    a rfl ids one hone (fun _ hi => hi) hlen hids h.oneBytes
    (hblank 149 (by decide)) (hblank 150 (by decide)) (hblank 151 (by decide))
    (hblank 854 (by decide)) (hblank 159 (by decide))
  refine ⟨out,k,⟨rr,Function.update a.stacks 854 (Product.bytes out)⟩,hout,?_,
    hk.trans (productBudget_le _ _ _ _ _ _ _ ids hlen),he,rfl,?_⟩
  · exact foldRel_product decode value step (fun _ _ _ hs => hs) hfold honedense
  · exact product_return_bound a _ out rfl h.incoming hout h.seedFits

/-- Full accepted-assignment execution: paid setup and the actual concrete
callback fold produce the specialized original factor product. The return
restores the fixed structural boundary P; prefix storage is bounded separately
by one fixed polynomial budget rather than fed into the next assignment. -/
theorem assignment_eval_correct {a : FactorAssignmentProgram.Data}
    (h : Entry q P M S a) (ids : List ℕ)
    (hids : a.stacks 175 = ProgramEncoding.encodeRecords (records ids))
    (width Z : ℕ)
    (hwidth : ∀ f (hf : f < q.rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length ≤ width)
    (hZ : 1 ≤ Z) (hP : P ≤ Z) (hbit : q.bitWidth ≤ Z)
    (hshape : d * baseWidth 3 q.p.t ≤ Z)
    (hhashScale : ∀ f (hf : f < q.rows.length),
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length ≤ Z)
    (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0 ≤ Z) :
    ∃ (out : Raw n (baseWidth 3 q.p.t) d) (steps : ℕ) (b : FactorAssignmentProgram.Data), NativeSemantics.Good ∅ q.u q.J out ∧
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode out =
        (ids.map (fun f => QueryEvaluation.specializeDense q.u q.J
          (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
          (q.value (a.stacks ∘ lowStack) f))).prod ∧
      steps ≤ assignmentBudget q P S Z ∧
      Eval assignment steps a b ∧
      b.stacks 854 = Product.bytes out ∧ WordBound P b ∧
      (∀ i : Fin 56,
        b.stacks (lowStack (Factor.nativeStacks (HashCircuitProgram.Native.Memory.lowPort i))) =
          IdempotentApplyProgram.Steps.low q.ctx i) ∧
      b.stacks 853 = a.stacks 853 ∧ b.stacks 883 = a.stacks 883 ∧
      b.stacks 884 = a.stacks 884 ∧
      (∀ i, i ∉ entryScratch → i ∉ cachePorts.map lowStack → i ≠ 854 →
        b.stacks i = a.stacks i) ∧
      Trace program (steps + 1) (a.withPC (some program.entry)) (b.withPC none) ∧
      (∀ j z, j ≤ steps + 1 → Trace program j (a.withPC (some program.entry)) z →
        dataBits z ≤ 896 * P + assignmentBudget q P S Z + 1) := by
  obtain ⟨prepared,hprepare,hready,hone,honeval,honedense,hretained,hblank⟩ := h.prepare
  have hpreparedIds : prepared.stacks 175 = ProgramEncoding.encodeRecords (records ids) :=
    (hretained 175 (by decide)).trans hids
  obtain ⟨out,k,b,hout,hvalue,hk,he,hframe,hbound⟩ :=
    prepared_product_eval_correct hready ids hone honeval honedense hpreparedIds hblank
      width Z hwidth hZ hP hbit hshape hhashScale hmarkScale
  have hrun := prepare_product_eval hprepare he
  have htime : prepareCost a + k ≤ assignmentBudget q P S Z := by
    have hp := prepareCost_le a P h.incoming
    unfold assignmentBudget
    omega
  have valueFrame (f : ℕ) : q.value (prepared.stacks ∘ lowStack) f =
      q.value (a.stacks ∘ lowStack) f := by
    have hj (j : ℕ) : Factor.factorJet q.p q.ps q.packing n f j q.theta
        (prepared.stacks ∘ lowStack) = Factor.factorJet q.p q.ps q.packing n f j q.theta
          (a.stacks ∘ lowStack) := by
      apply Factor.factorJet_frame
      all_goals exact hretained _ (by decide)
    unfold Factor.Spec.value Factor.Semantics.hashValue Factor.Semantics.markedValue
    simp_rw [hj]
  have frame (i : Fin 896) (hi : i ∉ entryScratch)
      (hc : i ∉ cachePorts.map lowStack) (h854 : i ≠ 854) : b.stacks i = a.stacks i := by
    rw [hframe,Function.update_of_ne h854]
    exact prepare_stack_frame hprepare i hi hc
  refine ⟨out,prepareCost a+k,b,hout,?_,htime,hrun,?_,hbound,?_,
    frame 853 (by decide) (by decide) (by decide),
    frame 883 (by decide) (by decide) (by decide),
    frame 884 (by decide) (by decide) (by decide),frame,
    compiled_halt_trace hrun 175 854,?_⟩
  · simpa only [hretained 857 (by decide),valueFrame] using hvalue
  · rw [hframe,Function.update_self]
  · intro i
    have hi : lowStack (Factor.nativeStacks (HashCircuitProgram.Native.Memory.lowPort i)) ≠ 854 := by
      intro heq
      have he := congrArg (fun j : Fin 896 => j.val) heq
      have hib := i.isLt
      simp only [lowStack,Factor.nativeStacks,HashCircuitProgram.Native.Memory.lowPort,
        Fin.val_castAdd, Fin.coe_ofNat_eq_mod] at he
      omega
    rw [hframe,Function.update_of_ne hi]
    exact hready.low i
  · intro j z hj hz
    have hg := trace_dataBits program hz
    have ha := StreamResources.dataBits_le_mul (a.withPC (some program.entry)) h.incoming
    change stackBits a.stacks ≤ 896 * P at ha
    change dataBits z ≤ stackBits a.stacks + j at hg
    omega

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect
