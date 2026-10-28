import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect

/-! The fixed accepted branch physically overlays the current assignment,
computes its whole specialized factor product, and adds that same dictionary
to the head sum. Its compact return cap is independent of its transient cost. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect

open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram MomentsProgram
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram FactorAssignmentBoundary QueryTupleState
open HighQueryAdapter TruncatedRingProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- These actual caller words remain live throughout repeated candidates. -/
def framePorts : List (Fin 896) := masterPorts ++
  [175,650,651,670,671,836,837,838,839,840,841,842,843,844,845,846,847,
    851,852,859,860,861,864,865,866,867,868,869,883,884]

theorem frame_not_entry (i : Fin 896) (hi : i ∈ framePorts) :
    i ∉ entryScratch := by
  have small : ∀ i ∈ framePorts,
      i ∉ ([149,150,151,159,854] ++ callbackScratch.map lowStack : List (Fin 896)) :=
    List.forall_iff_forall_mem.mp (by
      simp only [framePorts,masterPorts,List.forall_append,List.forall_cons]
      repeat' apply And.intro
      all_goals decide)
  have outside : ∀ i ∈ framePorts,
      i ∈ FactorTableProgram.protectedPorts ∨
      (i.val ≠ 62 ∧ (i.val < 340 ∨ 684 < i.val) ∧ i.val ≠ 881 ∧ i.val ≠ 882 ∧
        (i.val < 885 ∨ 892 < i.val)) := List.forall_iff_forall_mem.mp (by
      simp only [framePorts,masterPorts,List.forall_append,List.forall_cons]
      repeat' apply And.intro
      all_goals decide)
  have tail : ∀ i ∈ framePorts,
      i ∉ ([62,680,681,682,683,684,881,882] : List (Fin 896)) :=
    List.forall_iff_forall_mem.mp (by
      simp only [framePorts,masterPorts,List.forall_append,List.forall_cons]
      repeat' apply And.intro
      all_goals decide)
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · exact small i hi hm
  · rcases outside i hi with hp | ho
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨j,_,hj⟩ := List.mem_map.mp hm
        exact FactorTableProgram.basePort_outside i (Or.inl hp) ⟨j,hj⟩
      · exact tail i hi hm
    · have hw := written_bounds i (table_entry_written i hm)
      omega

theorem frame_exclusions (i : Fin 896) (hi : i ∈ framePorts) :
    i ∉ NativeOverlay.changed ∧ i ∉ entryScratch ∧
    i ∉ cachePorts.map lowStack ∧ i ∉ FactorEnvironment.environmentPorts ∧
    i ≠ 853 ∧ i ≠ 854 := by
  have small : ∀ i ∈ framePorts,
      i ∉ NativeOverlay.changed ∧ i ∉ cachePorts.map lowStack ∧
      i ∉ FactorEnvironment.environmentPorts ∧ i ≠ 853 ∧ i ≠ 854 :=
    List.forall_iff_forall_mem.mp (by
      simp only [framePorts,masterPorts,List.forall_append,List.forall_cons]
      repeat' apply And.intro
      all_goals decide)
  obtain ⟨ho,hc,he,hs,hp⟩ := small i hi
  exact ⟨ho,frame_not_entry i hi,hc,he,hs,hp⟩

/-- Each component is a measured cost of a polynomial local invocation. -/
def budget {r Q n d : ℕ} (q : Factor.Spec r Q n d) (P S Z : ℕ) : ℕ :=
  70*P+70 + FactorAssignmentCorrect.assignmentBudget q P S Z +
    TruncatedRingProgram.additionBudget n (baseWidth 3 q.p.t) d q.u q.J + 14*(896*P)+22

/-- The concrete accepted command has a fixed polynomial cost in its physical
boundary and the actual uniform factor-callback budget. The exponent is
independent of all runtime dimensions. -/
theorem budget_polynomial {r Q n d : ℕ} (q : Factor.Spec r Q n d) (P S Z : ℕ) :
    budget q P S Z ≤ 3020000 *
      (entryScratch.length + n + baseWidth 3 q.p.t + d + q.u + q.J + P +
        FactorAssignmentCallback.uniformCallbackBudget q P S Z + 1)^10 := by
  let X := entryScratch.length + n + baseWidth 3 q.p.t + d + q.u + q.J + P +
    FactorAssignmentCallback.uniformCallbackBudget q P S Z + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hP : P ≤ X := by dsimp [X]; omega
  have h0 : 1 ≤ X^10 := Nat.one_le_pow _ _ hX
  have h1 : X ≤ X^10 := by
    simpa using Nat.pow_le_pow_right hX (show 1 ≤ 10 by decide)
  have h4 : X^4 ≤ X^10 := Nat.pow_le_pow_right hX (by decide)
  have ha := FactorAssignmentCorrect.assignmentBudget_polynomial q P S Z
  change FactorAssignmentCorrect.assignmentBudget q P S Z ≤ 1600 * X^4 at ha
  have hd : n + baseWidth 3 q.p.t + d + q.u + q.J + 1 ≤ X := by dsimp [X]; omega
  have hb := (additionBudget_le_local n (baseWidth 3 q.p.t) d q.u q.J 0).trans
    (localBudget_le n (baseWidth 3 q.p.t) d q.u q.J 0)
  simp only [Nat.add_zero] at hb
  have hc : additionBudget n (baseWidth 3 q.p.t) d q.u q.J ≤ 3000000 * X^10 := by
    apply hb.trans
    gcongr
  change 70*P+70 + FactorAssignmentCorrect.assignmentBudget q P S Z +
    additionBudget n (baseWidth 3 q.p.t) d q.u q.J + 14*(896*P)+22 ≤ 3020000*X^10
  omega

/-- One input-polynomial envelope covers the compact boundary, actual gate,
and concrete accepted branch. It may be fixed once for every head iteration. -/
theorem body_envelope_polynomial {r Q n d : ℕ} (q : Factor.Spec r Q n d) (P S Z : ℕ) :
    896*P + HeadEvaluationProgram.StagedGate.bodyPolynomial P + budget q P S Z ≤
      3040000 * (entryScratch.length + n + baseWidth 3 q.p.t + d + q.u + q.J + P +
        FactorAssignmentCallback.uniformCallbackBudget q P S Z + 1)^10 := by
  let X := entryScratch.length + n + baseWidth 3 q.p.t + d + q.u + q.J + P +
    FactorAssignmentCallback.uniformCallbackBudget q P S Z + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hP : P+1 ≤ X := by dsimp [X]; omega
  have h1 : X ≤ X^10 := by
    simpa using Nat.pow_le_pow_right hX (show 1 ≤ 10 by decide)
  have h6 : X^6 ≤ X^10 := Nat.pow_le_pow_right hX (by decide)
  have hg : HeadEvaluationProgram.StagedGate.bodyPolynomial P ≤ 16000*X^6 := by
    apply (HeadEvaluationProgram.StagedGate.bodyPolynomial_le P).trans
    gcongr
  have ha := budget_polynomial q P S Z
  change budget q P S Z ≤ 3020000*X^10 at ha
  change 896*P + HeadEvaluationProgram.StagedGate.bodyPolynomial P + budget q P S Z ≤
    3040000*X^10
  omega

/-- Actual overlay execution, including its paid reset, with the exact ambient
assignment witness retained for the source-factor interpretation. -/
theorem overlay_eval {a : FactorAssignmentProgram.Data} {P n : ℕ}
    (ha : WordBound P a)
    (hh : (a.stacks 859).length = HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length = (a.stacks 869).length)
    (hn : (a.stacks 670).length = n) :
    ∃ steps b, Eval NativeOverlay.prepare steps a b ∧ steps ≤ 70*P+70 ∧
      WordBound P b ∧ (b.stacks 145).length = n ∧
      ∀ i, i ∉ NativeOverlay.changed → b.stacks i = a.stacks i := by
  have hbits := NativeOverlay.reset_frame a 859 (by decide)
  have hmask := NativeOverlay.reset_frame a 670 (by decide)
  have hbase := NativeOverlay.reset_frame a 869 (by decide)
  obtain ⟨rf,hc⟩ := NativeOverlay.command_eval (NativeOverlay.resetState a)
    (fun i hi => BankRoutines.clearBankStacks_mem i NativeOverlay.changed a.stacks hi)
    (by simpa only [hbits,hmask] using hh) (by simpa only [hmask,hbase] using hm)
  have he := (NativeOverlay.reset_eval a).seq hc
  obtain ⟨steps,rf',ht,hb,_⟩ := NativeOverlay.prepare_trace_space a P hh hm ha
  have ht' := compiled_halt_trace he 859 145
  have hsteps := StreamResources.halted_trace_steps_eq ht' ht (by rfl) (by rfl)
  refine ⟨_,_,he,by omega,NativeOverlay.prepared_bound a rf P hh ha,?_,
    NativeOverlay.prepared_frame a rf⟩
  exact (NativeOverlay.prepared_length a rf hh).trans hn

variable {r Q n d P M S : ℕ} {q : Factor.Spec r Q n d}

/-- There is no evaluator premise: all three stages are the fixed native
commands. The source product is interpreted at the actual overlaid state,
which the head invariant later identifies with its current Boolean candidate. -/
theorem accepted_eval {node : Fin Q} {H : Finset (Fin n)} {high : H → Bool}
    {E U : Finset (Fin n)} {a : FactorAssignmentProgram.Data}
    (hq : QueryReady q node H high E U M a) (ha : WordBound P a)
    (seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (hseed : Good ∅ q.u q.J seed) (hseedWord : a.stacks 853 = Product.bytes seed)
    (hlow : ∀ i : Fin 56, a.stacks (i.castAdd 840) = [])
    (hs0 : a.stacks 883 = []) (hs1 : a.stacks 884 = [])
    (hh : (a.stacks 859).length = HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length = (a.stacks 869).length)
    (hn : (a.stacks 670).length = n)
    (hcache : 4*M+6 ≤ P)
    (hcapacity : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J ≤ P)
    (hsize : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
      (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S)
    (hradius : q.p.R+1 ≤ Q)
    (ids : List ℕ) (hids : a.stacks 175 = ProgramEncoding.encodeRecords (FactorAssignmentLoop.records ids))
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
    ∃ (overlaySteps : ℕ) (overlaid : FactorAssignmentProgram.Data) (steps : ℕ) (b : FactorAssignmentProgram.Data)
      (out : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d),
      Eval NativeOverlay.prepare overlaySteps a overlaid ∧
      Eval HeadSumAssembly.accepted steps a b ∧ steps ≤ budget q P S Z ∧
      Good ∅ q.u q.J out ∧ b.stacks 853 = Product.bytes out ∧
      rawValue q.u q.J q.p.ops.decode out = rawValue q.u q.J q.p.ops.decode seed +
        QueryEvaluation.specializeDense q.u q.J
          (fun v => decide (v ∈ Squarefree.decodeMask n (overlaid.stacks 857)))
          (Squarefree.canonical q.u q.J ((ids.map (q.value (overlaid.stacks ∘ lowStack))).prod)) ∧
      WordBound P b ∧ QueryReady q node H high E U M b ∧
      (∀ i : Fin 56, b.stacks (i.castAdd 840) = []) ∧ b.stacks 854 = [] ∧
      (∀ i ∈ framePorts, b.stacks i = a.stacks i) ∧
      (∀ i, i ∉ NativeOverlay.changed → i ∉ entryScratch →
        i ∉ cachePorts.map lowStack → i ∉ FactorEnvironment.environmentPorts →
        i ≠ 853 → i ≠ 854 → b.stacks i = a.stacks i) ∧
      Trace (compiled HeadSumAssembly.accepted 859 853) (steps+1)
        (a.withPC (some (compiled HeadSumAssembly.accepted 859 853).entry)) (b.withPC none) ∧
      (∀ j z, j ≤ steps+1 → Trace (compiled HeadSumAssembly.accepted 859 853) j
        (a.withPC (some (compiled HeadSumAssembly.accepted 859 853).entry)) z →
        dataBits z ≤ 896*P + budget q P S Z + 1) := by
  obtain ⟨no,o,ho,hno,hob,hon,hof⟩ := overlay_eval ha hh hm hn
  have hom : QueryMasterFrame a o := ⟨fun i hi => hof i
    (frame_exclusions i (List.mem_append_left _ hi)).1⟩
  have hoq := hq.frame hom
  have holow (i : Fin 56) : o.stacks (i.castAdd 840) = [] := by
    rw [hof _ (by
      have := i.isLt
      simp only [NativeOverlay.changed,List.mem_cons,List.mem_nil_iff,or_false,not_or,
        Fin.ext_iff, Fin.val_castAdd, Fin.coe_ofNat_eq_mod]
      omega),hlow]
  have hentry := entry_of_query hoq hob hon holow hcache hcapacity hsize hradius
  have hoid : o.stacks 175 = ProgramEncoding.encodeRecords (FactorAssignmentLoop.records ids) :=
    (hof 175 (by decide)).trans hids
  obtain ⟨product,na,c,hgood,hvalue,hna,hassign,hproduct,hcb,hclow,
    hcseed,hcs0,hcs1,hcf,_,_⟩ := FactorAssignmentCorrect.assignment_eval_correct hentry ids hoid
      width Z hwidth hZ hP hbit hshape hhashScale hmarkScale
  have hproductGood : Good ∅ q.u q.J product := ⟨hgood.valid,hgood.nodup⟩
  have hcseed' : c.stacks 853 = Product.bytes seed :=
    hcseed.trans ((hof 853 (by decide)).trans hseedWord)
  have hcs0' : c.stacks 883 = [] := hcs0.trans ((hof 883 (by decide)).trans hs0)
  have hcs1' : c.stacks 884 = [] := hcs1.trans ((hof 884 (by decide)).trans hs1)
  have hclow' : ∀ i : Fin 56, c.stacks (i.castAdd 840) =
      Product.tapes (Product.idle q.p.modulus.bits q.width q.p.cache.zero.val
        (RingTriple.tableEncoding (HornerProgram.modelTable q.p.t q.p.model q.p.modulus q.p.cache))
        (List.replicate d true) (List.replicate q.u true) (List.replicate q.J true)) i := by
    intro i
    exact hclow i
  obtain ⟨ns,b,hns,hadd,hout,hstacks,hblank,_⟩ := HeadSumProgram.accumulate_eval 3 q.p.t
    q.p.modulus q.p.cache product seed hproductGood hseed c q.width (List.replicate d true)
    q.p.cache.zero.val
    (RingTriple.tableEncoding (HornerProgram.modelTable q.p.t q.p.model q.p.modulus q.p.cache))
    (List.replicate q.u true) (List.replicate q.J true) (by simp) q.widthLength
    hclow' hcseed' hproduct hcs0' hcs1'
  let out := Normalize.run 3 q.p.t q.p.modulus q.p.cache product seed
  have hrun : Eval HeadSumAssembly.accepted (no+(na+ns)) a b := ho.seq (hassign.seq hadd)
  have hmass : stackBits c.stacks ≤ 896*P :=
    StreamResources.dataBits_le_mul (c.withPC (none : Option (Fin 1))) hcb
  have hreset := FactorEnvironment.resetCost_le c
  have htime : no+(na+ns) ≤ budget q P S Z := by
    dsimp only [budget]
    omega
  have hb : WordBound P b := HeadAcceptedSpace.accumulate_return_bound 3 q.p.t
    q.p.modulus q.p.cache product seed hproductGood hseed c b q.width (List.replicate d true)
    q.p.cache.zero.val
    (RingTriple.tableEncoding (HornerProgram.modelTable q.p.t q.p.model q.p.modulus q.p.cache))
    (List.replicate q.u true) (List.replicate q.J true) (by simp) q.widthLength
    hclow' hcseed' hproduct hcs0' hcs1' hcapacity hcb hadd
  have frame (i : Fin 896) (ho : i ∉ NativeOverlay.changed) (he : i ∉ entryScratch)
      (hc : i ∉ cachePorts.map lowStack) (henv : i ∉ FactorEnvironment.environmentPorts)
      (h853 : i ≠ 853) (h854 : i ≠ 854) : b.stacks i = a.stacks i := by
    rw [hstacks,Function.update_of_ne h854,Function.update_of_ne h853,
      FactorEnvironment.reset_frame c i henv,hcf i he hc h854,hof i ho]
  have hframe (i : Fin 896) (hi : i ∈ framePorts) : b.stacks i = a.stacks i := by
    obtain ⟨ho,he,hc,henv,h853,h854⟩ := frame_exclusions i hi
    exact frame i ho he hc henv h853 h854
  refine ⟨no,o,no+(na+ns),b,out,ho,hrun,htime,hout,?_,?_,hb,
    hq.frame ⟨fun i hi => hframe i (List.mem_append_left _ hi)⟩,hblank,?_,
    hframe,frame,compiled_halt_trace hrun 859 853,?_⟩
  · simp [hstacks,out]
  · have hd := normalize_dense 3 q.p.t q.p.modulus q.p.cache
      (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
      q.u q.J product seed hseed.nodup
    change rawValue q.u q.J q.p.ops.decode out =
      rawValue q.u q.J q.p.ops.decode product + rawValue q.u q.J q.p.ops.decode seed at hd
    rw [hd,hvalue,FactorAssignmentCorrect.specialized_product,add_comm]
  · simp [hstacks]
  · intro j z hj hz
    have hg := trace_dataBits (compiled HeadSumAssembly.accepted 859 853) hz
    have hm := StreamResources.dataBits_le_mul
      (a.withPC (some (compiled HeadSumAssembly.accepted 859 853).entry)) ha
    change dataBits z ≤ stackBits a.stacks+j at hg
    change stackBits a.stacks ≤ 896*P at hm
    omega

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect
