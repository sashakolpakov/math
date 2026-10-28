import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality

/-! Correctness of the fixed head rescan. The invariant retains the current
normalized dictionary and the actual immutable source words. Its compact
boundary is reused after every candidate; no execution service is assumed. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram
open HeadIdentifierProgram BucketTupleProgram.Concrete
open QueryTupleState (masterPorts QueryMasterFrame QueryReady)
open scoped BigOperators

noncomputable section

/-- All words retained by one head, excluding its changing cursor and sum. -/
def retainedPorts : List (Fin 896) := masterPorts ++
  [175,650,651,670,671,836,837,838,839,840,841,842,843,844,845,846,847,
    851,852,864,865,866,867,868,869]

private theorem retained_exclusions (j : Fin 896) (hj : j ∈ retainedPorts) :
    56 ≤ j.val ∧ j ∉ HeadSumAssembly.controllerPorts ∧ j ≠ 853 ∧
      j ≠ 859 ∧ j ≠ 860 ∧ j ≠ 861 := by
  have h : ∀ j ∈ retainedPorts, 56 ≤ j.val ∧ j ∉ HeadSumAssembly.controllerPorts ∧
      j ≠ 853 ∧ j ≠ 859 ∧ j ≠ 860 ∧ j ≠ 861 :=
    List.forall_iff_forall_mem.mp (by
      simp only [retainedPorts,masterPorts,List.forall_append,List.forall_cons]
      repeat' apply And.intro
      all_goals decide)
  exact h j hj

private theorem retained_accepted (j : Fin 896) (hj : j ∈ retainedPorts) :
    j ∈ HeadAcceptedCorrect.framePorts := by
  have h : ∀ j ∈ retainedPorts, j ∈ HeadAcceptedCorrect.framePorts :=
    List.forall_iff_forall_mem.mp (by
      simp only [retainedPorts,masterPorts,List.forall_append,List.forall_cons]
      repeat' apply And.intro
      all_goals decide)
  exact h j hj

structure Accumulator {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (origin : HeadSumProgram.Data) (contribution : ℕ → Dense (q.p.model.O q.p.t) q.u q.J)
    (P i : ℕ) (a : HeadSumProgram.Data) : Prop where
  compact : ∀ j, (a.stacks j).length ≤ P
  retained : ∀ j ∈ retainedPorts, a.stacks j = origin.stacks j
  low : ∀ j : Fin 56, a.stacks (j.castAdd 840) = []
  scratch0 : a.stacks 883 = []
  scratch1 : a.stacks 884 = []
  partialSum : ∃ entries : List (Product.Entry n (baseWidth 3 q.p.t) d),
    Good ∅ q.u q.J entries ∧ a.stacks 853 = Product.bytes entries ∧
      rawValue q.u q.J q.p.ops.decode entries = ∑ j ∈ Finset.range i, contribution j

namespace Accumulator
variable {r Q n d : ℕ} {q : Factor.Spec r Q n d}
  {origin : HeadSumProgram.Data} {contribution : ℕ → Dense (q.p.model.O q.p.t) q.u q.J}
  {P i : ℕ} {a b : HeadSumProgram.Data}

theorem query {node : Fin Q} {H : Finset (Fin n)} {high : H → Bool}
    {E U : Finset (Fin n)} {M : ℕ}
    (ha : Accumulator q origin contribution P i a)
    (hq : QueryReady q node H high E U M origin) :
    QueryReady q node H high E U M a :=
  hq.frame ⟨fun j hj => ha.retained j (List.mem_append_left _ hj)⟩

theorem register_change (ha : Accumulator q origin contribution P i a)
    (regs : Fin 40 → Bool) : Accumulator q origin contribution P i ⟨regs,a.stacks⟩ :=
  ⟨ha.compact,ha.retained,ha.low,ha.scratch0,ha.scratch1,ha.partialSum⟩

theorem initial (q : Factor.Spec r Q n d) (a : HeadSumProgram.Data)
    (contribution : ℕ → Dense (q.p.model.O q.p.t) q.u q.J) (h P : ℕ)
    (hshape : a.stacks 651 = List.replicate h false)
    (ha : ∀ j, (a.stacks j).length ≤ P) (hh : h+1 ≤ P) :
    Accumulator q a contribution P 0
      (CounterForPrograms.testResult fuelPorts (seeded (HeadSumAssembly.cleared a))) := by
  have hs := HeadSumCorrect.initial_stacks a h hshape
  refine ⟨HeadSumCorrect.initial_word_bound a h P hshape ha hh, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨hl,hc,hsum,_,_,_⟩ := retained_exclusions j hj
    exact HeadSumFrames.initial_frame a h hshape j hl hc hsum
  · intro j
    rw [hs]
    have hv := j.isLt
    have h0 : j.castAdd 840 ≠ (853 : Fin 896) := by intro he; have := congrArg Fin.val he; simp at this; omega
    have h1 : j.castAdd 840 ≠ (860 : Fin 896) := by intro he; have := congrArg Fin.val he; simp at this; omega
    have h2 : j.castAdd 840 ≠ (859 : Fin 896) := by intro he; have := congrArg Fin.val he; simp at this; omega
    simp only [Function.update_of_ne h0,Function.update_of_ne h1,Function.update_of_ne h2]
    exact HeadSumAssembly.cleared_low a j
  · rw [hs]
    simp only [Function.update_of_ne (by decide : (883 : Fin 896) ≠ 853),
      Function.update_of_ne (by decide : (883 : Fin 896) ≠ 860),
      Function.update_of_ne (by decide : (883 : Fin 896) ≠ 859)]
    exact HeadSumAssembly.cleared_controller a 883 (by decide)
  · rw [hs]
    simp only [Function.update_of_ne (by decide : (884 : Fin 896) ≠ 853),
      Function.update_of_ne (by decide : (884 : Fin 896) ≠ 860),
      Function.update_of_ne (by decide : (884 : Fin 896) ≠ 859)]
    exact HeadSumAssembly.cleared_controller a 884 (by decide)
  · exact ⟨[],Good.nil,by rw [hs]; rfl,by simp⟩

/-- The semantic sum and immutable inputs survive the real increment and
countdown, including the terminal assignment overflow. -/
theorem advance {h rank : ℕ} (hc : Cursor h rank a)
    (hp : 0 < CounterPrograms.value (a.stacks 860))
    (hw : b.stacks 859 = a.stacks 859) (hf : b.stacks 860 = a.stacks 860)
    (hs : b.stacks 861 = []) (hb : Accumulator q origin contribution P i b)
    (hh : h+1 ≤ P) : Accumulator q origin contribution P i
      (CounterForPrograms.nextState fuelPorts (Counters.incrementResult cursorPorts b)) := by
  refine ⟨HeadSumCorrect.advance_word_bound hc hp hw hf hs hb.compact hh, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨_,_,_,h859,h860,h861⟩ := retained_exclusions j hj
    exact (HeadSumFrames.advance_frame b hs j h859 h860 h861).trans (hb.retained j hj)
  · intro j
    have hv := j.isLt
    have hx (k : Fin 896) (hk : 56 ≤ k.val) : j.castAdd 840 ≠ k := by
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_castAdd] at this
      omega
    rw [HeadSumFrames.advance_frame b hs _ (hx 859 (by decide))
      (hx 860 (by decide)) (hx 861 (by decide))]
    exact hb.low j
  · rw [HeadSumFrames.advance_frame b hs 883 (by decide) (by decide) (by decide)]
    exact hb.scratch0
  · rw [HeadSumFrames.advance_frame b hs 884 (by decide) (by decide) (by decide)]
    exact hb.scratch1
  · obtain ⟨entries,hg,hw,hv⟩ := hb.partialSum
    exact ⟨entries,hg,(HeadSumFrames.advance_frame b hs 853 (by decide) (by decide) (by decide)).trans hw,hv⟩

end Accumulator

/-- Exact physical high/mask words and the actual ambient overlay identify the
whole assignment product with the original free-variable source expression. -/
theorem actual_product_value {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool) (U : Finset (Fin n))
    (x : ResidualEmbedding.Free H → Bool) (a : HeadSumProgram.Data) (ids : List ℕ)
    (hmask : a.stacks 702 = List.ofFn (fun v : Fin n => decide (v ∈ H)))
    (hbits : a.stacks 703 = List.ofFn (fun v : Fin n => if h : v ∈ H then high ⟨v,h⟩ else false))
    (hU : a.stacks 857 = List.ofFn (fun v : Fin n => decide (v ∈ U)))
    (h145 : a.stacks 145 = List.ofFn (HighIncidence.glue H high x))
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0) :
    QueryEvaluation.specializeDense q.u q.J
      (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
      (Squarefree.canonical q.u q.J
        ((ids.map (q.value (a.stacks ∘ FactorAssignmentProgram.lowStack))).prod)) =
    QueryEvaluation.specializeDense q.u q.J
      (fun v : ResidualEmbedding.Free H => decide (v.val ∈ U))
      (HeadSourceLocality.sourceProduct q H high (HeadSourceLocality.stateFor H high x) ids) := by
  have hm (v : Fin n) : ((a.stacks ∘ FactorAssignmentProgram.lowStack) 702).getD v.val false =
      decide (v ∈ H) := by
    change (a.stacks 702).getD v.val false = _
    simp [hmask, List.getD_eq_getElem?_getD, v.isLt]
  have hb (v : H) : ((a.stacks ∘ FactorAssignmentProgram.lowStack) 703).getD v.val.val false = high v := by
    change (a.stacks 703).getD v.val.val false = _
    simp [hbits, List.getD_eq_getElem?_getD, v.val.isLt, v.property]
  have hd : Squarefree.decodeMask n (a.stacks 857) = U := by
    rw [hU]
    exact Squarefree.decodeMask_encodeMask U
  rw [hd,QueryJetSemantics.actualProduct_specializeDense q H high _ hm hb hzero ids
    (fun v => decide (v ∈ U)) (fun v : ResidualEmbedding.Free H => decide (v.val ∈ U))
    (fun _ => rfl)]
  exact congrArg (QueryEvaluation.specializeDense q.u q.J
    (fun v : ResidualEmbedding.Free H => decide (v.val ∈ U)))
    (HeadSourceLocality.sourceProduct_assignment_word q H high _
      (HeadSourceLocality.stateFor H high x) h145 ids)

/-- The fixed head program produces the exact restricted signature-fiber sum.
Both resource bounds refer to this same run; every retained stack is counted. -/
theorem run {r Q n d M P S Z : ℕ} (q : Factor.Spec r Q n d)
    (node : Fin Q) (H E U : Finset (Fin n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (g : Fin r) (pick : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds pick n ↔ ∃ _ : v ∉ H, head node v = g)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) k → Bool)
    (W : List Bool) (c : Fin q.ps.length → Fin (count pick n) → List Bool)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) +
        LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R node j.val
          ((chosenIds pick n).get i))
    (ids : List ℕ) (a : HeadSumProgram.Data)
    (hq : QueryReady q node H high E U M a) (ha : ∀ j, (a.stacks j).length ≤ P)
    (hshape : a.stacks 651 = List.replicate (count pick n) false)
    (hmask : a.stacks 670 = List.ofFn (fun v : Fin n => pick v.val))
    (hbase : a.stacks 869 = List.ofFn (HighIncidence.glue H high
      (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val) reps)))
    (hW : a.stacks 864 = W)
    (hmatrix : a.stacks 865 = OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words
      ((List.ofFn (fun j => List.ofFn (c j))).map OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words))
    (hkey : a.stacks 866 = BucketProgram.signatureValue W
      (List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
        (chosenIds_bound pick n) (chosenIds_nodup pick n) hs (reps g)))
      (List.ofFn (fun j => List.ofFn (c j))))
    (hE : a.stacks 867 = HighIncidenceProgram.Restriction.selected true
      (List.ofFn (fun v : Fin n => pick v.val)) (LeafWeightProgram.supportBits ⟨E⟩))
    (hH : a.stacks 868 = List.replicate (count pick n) true)
    (hids : a.stacks 175 = ProgramEncoding.encodeRecords (FactorAssignmentLoop.records ids))
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
    (hcount : count pick n+1 ≤ P) (hrows : q.ps.length ≤ P)
    (hcoeff : ∀ j i, (c j i).length ≤ P)
    (hcache : 4*M+6 ≤ P)
    (hcapacity : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J ≤ P)
    (hsize : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
      (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S)
    (hradius : q.p.R+1 ≤ Q) (width : ℕ)
    (hwidth : ∀ f (hf : f < q.rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length ≤ width)
    (hZ : 1 ≤ Z) (hP : P ≤ Z) (hbit : q.bitWidth ≤ Z)
    (hdegree : d * baseWidth 3 q.p.t ≤ Z)
    (hhashScale : ∀ f (hf : f < q.rows.length),
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length ≤ Z)
    (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0 ≤ Z)
    (B : ℕ)
    (hlocal : 896*P + HeadEvaluationProgram.StagedGate.bodyPolynomial P +
      HeadAcceptedCorrect.budget q P S Z ≤ B)
    (hcounter : 9*(count pick n+1)+8 ≤ B) :
    ∃ steps b, ∃ entries : List (Product.Entry n (baseWidth 3 q.p.t) d),
      Trace HeadAcceptedProgram.program steps
        (a.withPC (some HeadAcceptedProgram.program.entry)) (b.withPC none) ∧
      Eval (HeadSumAssembly.head HeadSumAssembly.accepted) (steps-1) a b ∧
      Good ∅ q.u q.J entries ∧ b.stacks 853 = Product.bytes entries ∧
      rawValue q.u q.J q.p.ops.decode entries =
        (∑ x : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool,
          if HeadSourceLocality.freeLabel q.p q.ps q.packing owner head H node g x =
              HeadSourceLocality.freeLabel q.p q.ps q.packing owner head H node g (reps g) ∧
              (∀ v, v.val.val ∈ E → x v = true) then
            QueryEvaluation.specializeDense q.u q.J
              (fun v : ResidualEmbedding.Free H => decide (v.val ∈ U))
              (HeadSourceLocality.sourceProduct q H high
                (HeadSourceLocality.stateFor H high
                  (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val)
                    (Function.update reps g x))) ids) else 0) ∧
      (∀ j ∈ retainedPorts, b.stacks j = a.stacks j) ∧
      (∀ j, (b.stacks j).length ≤ P) ∧
      b.stacks 859 = [] ∧ b.stacks 860 = [] ∧ b.stacks 861 = [] ∧
      steps ≤ (2*(HeadEvaluationProgram.StagedGate.bodyPolynomial P +
        HeadAcceptedCorrect.budget q P S Z)+126*B+54*count pick n+286)*2^(count pick n) ∧
      ∀ elapsed z, elapsed ≤ steps → Trace HeadAcceptedProgram.program elapsed
        (a.withPC (some HeadAcceptedProgram.program.entry)) z →
        ∀ j, (z.stacks j).length ≤ B := by
  classical
  let h := count pick n
  let rows := List.ofFn (fun j => List.ofFn (c j))
  let order := freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
    (chosenIds_bound pick n) (chosenIds_nodup pick n) hs
  let candidate (i : Fin (2^h)) := order.symm (AttainedSignatures.assignmentEquiv h i)
  let value (x : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool) :=
    QueryEvaluation.specializeDense q.u q.J
      (fun v : ResidualEmbedding.Free H => decide (v.val ∈ U))
      (HeadSourceLocality.sourceProduct q H high (HeadSourceLocality.stateFor H high
        (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val)
          (Function.update reps g x))) ids)
  let selected (x : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool) :=
    HeadSourceLocality.freeLabel q.p q.ps q.packing owner head H node g x =
      HeadSourceLocality.freeLabel q.p q.ps q.packing owner head H node g (reps g) ∧
      ∀ v, v.val.val ∈ E → x v = true
  let contribution (i : ℕ) := if hi : i < 2^h then
    if selected (candidate ⟨i,hi⟩) then value (candidate ⟨i,hi⟩) else 0 else 0
  let I := fun i b => Cursor h i b ∧ Accumulator q a contribution P i b
  let C := HeadEvaluationProgram.StagedGate.bodyPolynomial P + HeadAcceptedCorrect.budget q P S Z
  have hi : I 0 (CounterForPrograms.testResult fuelPorts (seeded (HeadSumAssembly.cleared a))) := by
    refine ⟨?_,Accumulator.initial q a contribution h P hshape ha hcount⟩
    have hst := HeadSumCorrect.initial_stacks a h hshape
    apply Cursor.initial
    · simp [hst]
    · simp [hst]
    · simp only [hst,Function.update_of_ne (by decide : (861 : Fin 896) ≠ 853),
        Function.update_of_ne (by decide : (861 : Fin 896) ≠ 860),
        Function.update_of_ne (by decide : (861 : Fin 896) ≠ 859)]
      exact HeadSumAssembly.cleared_controller a 861 (by decide)
  have spec : ∀ i state, I i state → state.stacks 861 = [] →
      0 < CounterPrograms.value (state.stacks 860) →
      ∃ nb e, nb ≤ C ∧ Eval (body HeadSumAssembly.accepted) nb state e ∧
        e.stacks 860 = state.stacks 860 ∧ e.stacks 861 = [] ∧
        I (i+1) (CounterForPrograms.nextState fuelPorts e) := by
    intro i state hi hscratch hfuel
    obtain ⟨hcur,hacc⟩ := hi
    have hrank := hcur.index_lt hfuel
    let x := candidate ⟨i,hrank⟩
    have hbits : state.stacks 859 = List.ofFn (order x) := by
      have horder : order x = AttainedSignatures.assignmentEquiv h ⟨i, hrank⟩ := by
        dsimp only [x, candidate]
        exact Equiv.apply_symm_apply order _
      rw [horder]
      exact hcur.assignment_word hfuel
    have hfixed (j : Fin 896) (hj : j ∈ retainedPorts) := hacc.retained j hj
    have hmat : state.stacks 865 = OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words
        (rows.map OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words) := (hfixed 865 (by decide)).trans hmatrix
    have hlen : ∀ row ∈ rows, row.length = (state.stacks 859).length := by
      intro row hrow
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hrow
      simp [hcur.activeWidth hrank,h]
    have hEl : (state.stacks 859).length = (state.stacks 867).length := by
      rw [hfixed 867 (by decide),hE,HeadRepresentativeSemantics.selected_supportBits]
      simp [LeafWeightProgram.supportBits,hcur.activeWidth hrank,h]
    have hHl : (state.stacks 859).length = (state.stacks 868).length := by
      rw [hfixed 868 (by decide),hH,List.length_replicate,hcur.activeWidth hrank]
    have hgate : gateValue state rows = true ↔ selected x :=
      HeadSumCorrect.gate_source_iff q.p q.ps q.packing owner head H E node g pick hs W c hc
        x (reps g) state ((hfixed 864 (by decide)).trans hW) hbits
        ((hfixed 866 (by decide)).trans hkey) ((hfixed 867 (by decide)).trans hE)
        ((hfixed 868 (by decide)).trans hH)
    obtain ⟨nb,b,hnb,he,h859,h860,h861,hnext⟩ := body_eval HeadSumAssembly.accepted
      state rows (HeadAcceptedCorrect.budget q P S Z)
      (Accumulator q a contribution P (i+1))
      (fun j => hacc.low (j.castAdd 24)) hmat hlen hEl hHl hscratch
      (by
        intro hg out hout
        let start : HeadSumProgram.Data := ⟨out,state.stacks⟩
        have hsacc := hacc.register_change out
        obtain ⟨seed,hgood,hseed,hpartial⟩ := hsacc.partialSum
        have hsmask : start.stacks 670 = List.ofFn (fun v : Fin n => pick v.val) :=
          (hfixed 670 (by decide)).trans hmask
        have hsbase : start.stacks 869 = List.ofFn (HighIncidence.glue H high
            (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val) reps)) :=
          (hfixed 869 (by decide)).trans hbase
        have hh : (start.stacks 859).length = HighIncidenceProgram.Restriction.highCount (start.stacks 670) := by
          rw [hsmask,HeadRepresentativeSemantics.headOrder_highCount]
          exact hcur.activeWidth hrank
        have hm : (start.stacks 670).length = (start.stacks 869).length := by simp [hsmask,hsbase]
        have hn : (start.stacks 670).length = n := by simp [hsmask]
        obtain ⟨no,o,ns,b,entries,hover,haccepted,ht,hgood',hword,hvalue,hbound,hquery,
          hlow,h854,hframe,_,_,_⟩ := HeadAcceptedCorrect.accepted_eval
            (hsacc.query hq) hsacc.compact seed hgood hseed hsacc.low hsacc.scratch0 hsacc.scratch1
            hh hm hn hcache hcapacity hsize hradius ids
            ((hfixed 175 (by decide)).trans hids) width Z hwidth hZ hP hbit hdegree hhashScale hmarkScale
        have hom : QueryMasterFrame start o := ⟨fun j hj =>
          HeadSumFrames.overlay_frame hh hm hover j
            (HeadAcceptedCorrect.frame_exclusions j (List.mem_append_left _ hj)).1⟩
        have hoq := (hsacc.query hq).frame hom
        have h145 := HeadSumCorrect.prepared_head_update H high (head node) g pick hs reps x
          start o hover hbits hsmask hsbase
        have hv := actual_product_value q H high U
          (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val)
            (Function.update reps g x)) o ids hoq.highMask hoq.highBits hoq.inner h145 hzero
        have hcontribution : contribution i = value x := by simp [contribution,hrank,hgate.mp hg,x]
        refine ⟨ns,b,ht,haccepted,hframe 859 (by decide),hframe 860 (by decide),
          (hframe 861 (by decide)).trans hscratch,?_⟩
        refine ⟨hbound,fun j hj => (hframe j (retained_accepted j hj)).trans (hacc.retained j hj),
          hlow,(hframe 883 (by decide)).trans hacc.scratch0,
          (hframe 884 (by decide)).trans hacc.scratch1,entries,hgood',hword,?_⟩
        rw [hpartial,hv] at hvalue
        simpa only [Finset.sum_range_succ,hcontribution] using hvalue)
      (by
        intro hg out
        have hn : ¬ selected x := by intro hx; have := hgate.mpr hx; simp [hg] at this
        have hcontribution : contribution i = 0 := by simp [contribution,hrank,hn,x]
        obtain ⟨entries,hgood,hword,hvalue⟩ := hacc.partialSum
        refine ⟨hacc.compact,hacc.retained,hacc.low,hacc.scratch0,hacc.scratch1,
          entries,hgood,hword,?_⟩
        simpa only [Finset.sum_range_succ,hcontribution,add_zero] using hvalue)
    have hcost : bodyBudget state rows (HeadAcceptedCorrect.budget q P S Z) ≤ C := by
      apply HeadEvaluationProgram.StagedGate.bodyBudget_uniform state rows P _ hmat hlen
      · intro row hrow word hword
        obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hrow
        obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hword
        exact hcoeff j k
      · simpa [rows] using hrows
      · exact hacc.compact
    refine ⟨nb,Counters.incrementResult cursorPorts b,hnb.trans hcost,he,?_,?_,
      body_cursor_next hcur hfuel h859 h860 h861,
      Accumulator.advance hcur hfuel h859 h860 h861 hnext hcount⟩
    · rw [Counters.incrementResult_stacks cursorPorts b h861]
      simpa [cursorPorts] using h860
    · exact Counters.incrementResult_scratch cursorPorts b
  obtain ⟨steps,e,hrun,heval,hfinal,hsum,h859,h860,h861,htime,hspace⟩ :=
    HeadAcceptedSpace.head_resources_of_local_time HeadSumAssembly.accepted I h P B C
      (fun _ _ hi => hi.1) (fun _ _ hi => hi.2.compact) (by omega) hcounter spec
      a hshape (fun j => (ha j).trans (by omega)) hi
  obtain ⟨entries,hgood,hword,hvalue⟩ := hfinal.2.partialSum
  have hreindex := HeadSumCorrect.counter_sum_eq_head H
    (fun v : ResidualEmbedding.Free H => head node v.val) g pick hs
    (fun x => if selected x then value x else 0)
  have hout : rawValue q.u q.J q.p.ops.decode entries =
      ∑ x, if selected x then value x else 0 := hvalue.trans (by
        simpa only [contribution,candidate,order,h] using hreindex)
  refine ⟨steps,finalized e,entries,hrun,heval,hgood,hsum.trans hword,hout,?_,?_,
    h859,h860,h861,htime,hspace⟩
  · intro j hj
    obtain ⟨_,_,_,hj859,hj860,_⟩ := retained_exclusions j hj
    simpa only [finalized_stacks,Function.update_of_ne hj860,Function.update_of_ne hj859]
      using hfinal.2.retained j hj
  · have hb := finalize_prefix (finalize_eval e) hfinal.2.compact
    exact hb _ _ le_rfl (compiled_trace (finalize_eval e) 854 853)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative
