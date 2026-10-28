import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames

/-! Correctness of the fixed concrete two-pass visitor. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
open OAI BitProgram StructuredCalls
abbrev Data := State 40 896

open OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SubexpSetupStorage

private theorem emptyReplayCost (a : Data) (B : ℕ) (ha : WordBound B a) :
    restartCost a+2≤18*B+18 := by
  have h1:=ha 840
  have h2:=ha 837
  have h3:=ha 843
  have h4:=ha 845
  unfold restartCost
  omega

private theorem emptyReplay_registers (a : Data) (h : a.stacks 841=[]) (i : Fin 40)
    (hi : 16≤ i.val) : (tested (restartState a)).regs i=a.regs i := by
  have h0 : i≠0 := by intro he; subst i; simp at hi
  have h1 : i≠1 := by intro he; subst i; simp at hi
  have hr := CommandRegisterFrames.eval_register_frame (restart_eval a h) i
    (QueryVisitorFrames.restart_not_mem_writes i hi)
  exact (StackRoutines.readRegs_frame _ _ _ _ _ h0 h1).trans hr

/-- With no emitted heads the fixed visitor still constructs and contributes
the ring unit. Both real replay paths and the real normalization tail execute;
there is no empty-formula Boolean shortcut. -/
theorem visitor_empty {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {P B : ℕ} {a : Data} {value : Truncated (q.p.model.O q.p.t) q.J}
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q value a)
    (ha : WordBound B a) (hPB : 4*P+6≤B) (hreps : a.stacks 837=[])
    (hcap : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2)≤B) :
    ∃ steps b, Eval visitor steps a b ∧ QueryReady q node H high E U P b ∧
      PairAccumulatorMeaning q (value+Dense.readout (1 : Dense (q.p.model.O q.p.t) q.p.t q.J)) b ∧
      WordBound B b ∧ QueryMasterFrame a b ∧
      (∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i) ∧
      (∀ i,16≤ i.val → b.regs i=a.regs i) ∧
      (∀ i∈SignatureTupleProgram.currentHeadPorts,b.stacks i=[]) ∧
      b.stacks 649=a.stacks 649 ∧
      steps+1≤QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J B+1600*(B+1) ∧
      QueryExecution.PrefixBound visitor (steps+1) a
        (896*B+QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J B+1600*(B+1)) := by
  obtain ⟨nt,a1,ht,hr1,hm1,hi,hb1,hcost1,entries,he,hg,hv⟩ :=
    QueryTupleState.initialize_run hr hm ha hPB
  have hreps1 : a1.stacks 837=[] := (hi.frame 837 (by decide)).trans hreps
  have hpass1 := QueryExecution.replay_nil baselineHead a1 hreps1 hi.scratch
  let a2 := tested (restartState a1)
  have hf2 (i : Fin 896) (h840 : i≠840) (h843 : i≠843) : a2.stacks i=a1.stacks i :=
    restartState_frame a1 i h840 h843
  have hb2 : WordBound B a2 := restartState_bound a1 B hb1
  have hr2 : QueryReady q node H high E U P a2 := hr1.frame (replay_masterFrame a1)
  have hm2 : PairAccumulatorMeaning q value a2 := hm1.frame (hf2 851 (by decide) (by decide))
  have hreps2 : a2.stacks 837=[] := (hf2 837 (by decide) (by decide)).trans hreps1
  have hscratch2 : a2.stacks 841=[] := (hf2 841 (by decide) (by decide)).trans hi.scratch
  have hpass2 := QueryExecution.replay_nil evaluateHead a2 hreps2 hscratch2
  let a3 := tested (restartState a2)
  have hf3 (i : Fin 896) (h840 : i≠840) (h843 : i≠843) : a3.stacks i=a2.stacks i :=
    restartState_frame a2 i h840 h843
  have hb3 : WordBound B a3 := restartState_bound a2 B hb2
  have hr3 : QueryReady q node H high E U P a3 := hr2.frame (replay_masterFrame a2)
  have hm3 : PairAccumulatorMeaning q value a3 := hm2.frame (hf3 851 (by decide) (by decide))
  have he3 : a3.stacks 852=Product.bytes entries :=
    (hf3 852 (by decide) (by decide)).trans ((hf2 852 (by decide) (by decide)).trans he)
  obtain ⟨nf,b,hfinish,hrb,hmb,hbb,hmasters,hcurrent,hframe,hregs,hcostf⟩ :=
    QueryTupleState.finish hr3 hm3 entries hg he3 hb3 hcap
  have heval : Eval visitor (nt+(restartCost a1+2+(restartCost a2+2+nf))) a b :=
    ht.seq (hpass1.1.seq (hpass2.1.seq hfinish))
  have hcost2 := emptyReplayCost a1 B hb1
  have hcost3 := emptyReplayCost a2 B hb2
  have hcost : nt+(restartCost a1+2+(restartCost a2+2+nf))+1≤
      QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J B+1600*(B+1) := by omega
  refine ⟨_,b,heval,hrb,?_,hbb,?_,?_,?_,hcurrent,?_,hcost,?_⟩
  · simpa only [hv] using hmb
  · exact (initialized_masterFrame hi).trans
      ((replay_masterFrame a1).trans ((replay_masterFrame a2).trans hmasters))
  · intro i hi'
    have hs : 128≤ i.val ∧ i∉SignatureTupleProgram.currentHeadPorts ∧ i≠851 ∧ i≠852 ∧
        i≠840 ∧ i≠843 ∧ i∉QueryTupleInit.changed := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
      rcases hi' with rfl|rfl|rfl|rfl
      all_goals decide
    exact (hframe i hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1).trans
      ((hf3 i hs.2.2.2.2.1 hs.2.2.2.2.2.1).trans
        ((hf2 i hs.2.2.2.2.1 hs.2.2.2.2.2.1).trans (hi.frame i hs.2.2.2.2.2.2)))
  · intro i hi'
    exact (hregs i hi').trans ((emptyReplay_registers a2 hscratch2 i hi').trans
      ((emptyReplay_registers a1 hi.scratch i hi').trans
        (QueryTupleInit.command_register_frame ht i hi')))
  · exact (hframe 649 (by decide) (by decide) (by decide) (by decide)).trans
      ((hf3 649 (by decide) (by decide)).trans
        ((hf2 649 (by decide) (by decide)).trans (hi.frame 649 (by decide))))
  · exact (QueryExecution.prefix_local visitor _ B a ha).mono (by omega)


/-- Concrete multiplication preserves the retained query snapshot. Its
changing head/tuple dictionaries are separate from the pair accumulator. -/
theorem multiply_masterFrame {a b : Data}
    (hf : ∀ i,i∉QueryAssembler.pairScratch → i≠61 → i≠70 → i≠852 → i≠853 →
      b.stacks i=a.stacks i) : QueryMasterFrame a b := by
  constructor
  intro i hi
  have hs : i∉QueryAssembler.pairScratch ∧ i≠61 ∧ i≠70 ∧ i≠852 ∧ i≠853 := by
    simp only [masterPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact hf i hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2

/-- The fixed native multiply consumes the actual head sum and retains its
full dense product. Readout is deferred until the completed tuple is added. -/
theorem multiply_run {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P B : ℕ}
    {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {left right : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
    (hl : DenseWord q 852 left a) (hh : DenseWord q 853 right a)
    (ha : WordBound B a)
    (hcap : FactorProductSpace.byteBound n (baseWidth 3 q.p.t) d q.p.t q.J≤B) :
    ∃ steps b, Eval QueryAssembler.TupleMultiply.command steps a b ∧
      QueryReady q node H high E U P b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 (left*right) b ∧ b.stacks 853=[] ∧ QueryMasterFrame a b ∧
      WordBound B b ∧
      (∀ i,i∉QueryAssembler.pairScratch → i≠61 → i≠70 → i≠852 → i≠853 →
        b.stacks i=a.stacks i) ∧
      (∀ i,16≤ i.val → b.regs i=a.regs i) ∧
      steps+1≤51000*(B+1)+FactorProductSpace.budget n (baseWidth 3 q.p.t) d q.p.t q.J ∧
      QueryExecution.PrefixBound QueryAssembler.TupleMultiply.command (steps+1) a
        (896*B+51000*(B+1)+FactorProductSpace.budget n (baseWidth 3 q.p.t) d q.p.t q.J) := by
  obtain ⟨seed,hseed,hseedGood,hleft⟩:=hl.entries
  obtain ⟨head,hhead,hheadGood,hright⟩:=hh.entries
  have henv : QueryAssembler.TupleMultiply.environment a=
      Product.idle q.p.modulus.bits q.width q.p.cache.zero.val
        (RingTriple.tableEncoding q.ctx.table) (a.stacks 204)
        (List.replicate q.p.t true) (List.replicate q.J true) := by
    unfold QueryAssembler.TupleMultiply.environment
    rw [hr.modulus,hr.width,hr.scalarZero,hr.table,hr.precision,hr.order]
    rfl
  obtain ⟨steps,b,he,_,houtput,hzero,hframe,hb,hcost,_,_⟩:=
    QueryAssembler.TupleMultiply.command_eval 3 q.p.t q.p.modulus q.p.cache q.p.hz q.ctx.table
      (a.stacks 204) q.width hr.degree_length q.widthLength seed head hseedGood hheadGood a B
      henv hseed hhead ha hcap
  have hf:=multiply_masterFrame hframe
  have hv:=DenseWord.multiplied q seed head hseedGood hheadGood b 852 houtput
  rw [hleft,hright] at hv
  refine ⟨steps,b,he,hr.frame hf,hm.frame (hframe 851 (by decide) (by decide) (by decide)
    (by decide) (by decide)),hv,hzero,hf,hb,hframe,?_,hcost,?_⟩
  · intro i hi
    exact CommandRegisterFrames.eval_register_frame he i
      (QueryVisitorFrames.tupleMultiply_not_mem_writes i hi)
  · exact (QueryExecution.prefix_local QueryAssembler.TupleMultiply.command _ B a ha).mono (by omega)

theorem headState_masterFrame (a : Data) (word tail address : List Bool) :
    QueryMasterFrame a (headState a word tail address) := by
  constructor
  intro i hi
  have hs : i≠838 ∧ i≠840 ∧ i≠843 := by
    simp only [masterPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact headState_frame a word tail address i hs.1 hs.2.1 hs.2.2

theorem finishHead_masterFrame (a : Data) : QueryMasterFrame a (finished a) := by
  constructor
  intro i hi
  have hne : i≠838 := by
    intro he
    subst i
    exact (by decide : (838 : Fin 896)∉masterPorts) hi
  rw [finished_stacks,Function.update_of_ne hne]

theorem installed_masterFrame (a : Data) (rf : Fin 8 → Bool) :
    QueryMasterFrame a (installedRepresentative a rf) := by
  constructor
  intro i hi
  have hs : i∉([145,859,869,872,873,874,875,876,877] : List (Fin 896)) := by
    simp only [masterPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact installedRepresentative_frame a rf i hs

/-- Parsing a retained representative frame restores the same word bound.
The decoded word and the remaining address are portions of actual stored
words, so their numerical values never become a storage charge. -/
theorem readHead_state_bound {base B : ℕ} {word : List Bool}
    {rest : List (List Bool)} {a : Data}
    (hc : FrameCursor base (word::rest) a) (ha : WordBound B a) :
    WordBound B (headState a word (suspendedFrames rest)
      (List.replicate (base+rest.length) true)) := by
  have hword := QueryExecution.cursor_word_length hc ha
  have hrest : (suspendedFrames rest).length≤B := by
    have hh:=ha 840
    rw [hc.frames] at hh
    simp only [SignatureTupleProgram.suspendedFrames,List.flatMap_cons,List.length_append] at hh
    exact (Nat.le_add_left _ _).trans hh
  have haddress : base+rest.length≤B := by
    have hh:=ha 843
    rw [hc.address] at hh
    simp only [List.length_replicate,List.length_cons] at hh
    omega
  intro i
  by_cases h838 : i=838
  · subst i
    rw [(headState_words ..).1]
    exact hword
  by_cases h840 : i=840
  · subst i
    rw [(headState_words ..).2.1]
    exact hrest
  by_cases h843 : i=843
  · subst i
    rw [(headState_words ..).2.2,List.length_replicate]
    exact haddress
  rw [headState_frame _ _ _ _ i h838 h840 h843]
  exact ha i

/-- The first-pass native overlay updates only the ambient representative
baseline. All ring inputs, the tuple product and the pair accumulator retain
their actual words and denotations. -/
theorem install_run {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P B : ℕ}
    {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
    (hv : DenseWord q 852 tupleValue a) (ha : WordBound B a)
    (htmp : a.stacks 841=[])
    (hh : (a.stacks 838).length=HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hmask : (a.stacks 670).length=(a.stacks 869).length) :
    ∃ steps rf, Eval installRepresentative steps a (installedRepresentative a rf) ∧
      QueryReady q node H high E U P (installedRepresentative a rf) ∧
      PairAccumulatorMeaning q pairValue (installedRepresentative a rf) ∧
      DenseWord q 852 tupleValue (installedRepresentative a rf) ∧
      QueryMasterFrame a (installedRepresentative a rf) ∧
      WordBound B (installedRepresentative a rf) ∧
      (installedRepresentative a rf).stacks 869=
        LeafAssignmentMergeProgram.merge
          (HighIncidenceProgram.Restriction.zeroMerge (a.stacks 670) (a.stacks 838))
          (a.stacks 670) (a.stacks 869) ∧
      (∀ i : Fin 40,16 ≤ i.val → (installedRepresentative a rf).regs i=a.regs i) ∧
      steps≤90*B+89 ∧
      QueryExecution.PrefixBound installRepresentative steps a (986*B+89) := by
  obtain ⟨steps,rf,he,ht⟩ := installRepresentative_eval a B htmp hh hmask ha
  have hf:=installed_masterFrame a rf
  refine ⟨steps,rf,he,hr.frame hf,
    hm.frame (installedRepresentative_frame a rf 851 (by decide)),
    hv.frame (installedRepresentative_frame a rf 852 (by decide)),hf,
    installedRepresentative_bound a rf B hh ha,installedRepresentative_baseline a rf,?_,ht,?_⟩
  · intro i hi
    exact CommandRegisterFrames.eval_register_frame he i
      (QueryVisitorFrames.install_not_mem_writes i hi)
  · exact (QueryExecution.prefix_local installRepresentative steps B a ha).mono (by omega)

theorem prepared_masterFrame (a : Data) (kr : Fin 8 → Bool) (sr : Fin 4 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool)))
    (hW : a.stacks 141=W) (hbits : a.stacks 838=bits)
    (hrows : a.stacks 847=Subexp.MatrixProgramSupport.words
      (rows.map Subexp.MatrixProgramSupport.words)) :
    QueryMasterFrame a (SignatureHeadPrepare.result a kr sr W bits rows) := by
  constructor
  intro i hi
  have hs : i∉SignatureHeadPrepare.cleared ∧ i≠864 ∧ i≠865 ∧ i≠175 ∧
      i∉HighQueryAdapter.NativeHeadSelect.changed := by
    simp only [masterPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact SignatureHeadPrepare.result_frame a kr sr W bits rows hW hbits hrows i
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2

/-- The actual full-key and correction-gate setup preserves the three
semantic invariants needed by the subsequent head sum and multiplication. -/
theorem prepare_run {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P B : ℕ}
    {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
    (hv : DenseWord q 852 tupleValue a) (ha : WordBound B a)
    (W bits : List Bool) (rows : List (List (List Bool)))
    (hW : a.stacks 141=W) (hbits : a.stacks 838=bits)
    (hrows : a.stacks 847=Subexp.MatrixProgramSupport.words
      (rows.map Subexp.MatrixProgramSupport.words))
    (hrowlen : ∀ row∈rows,row.length=bits.length)
    (hlen : (a.stacks 670).length=(a.stacks 858).length)
    (hkey : 16*(W.length+bits.length+
      (Subexp.MatrixProgramSupport.words (rows.map Subexp.MatrixProgramSupport.words)).length)+
      AttainedSignatureProgram.cost W bits rows+1≤B)
    (hselect : 11*(a.stacks 670).length+6≤B) :
    ∃ steps kr sr, Eval SignatureHeadPrepare.command steps a
        (SignatureHeadPrepare.result a kr sr W bits rows) ∧
      QueryReady q node H high E U P (SignatureHeadPrepare.result a kr sr W bits rows) ∧
      PairAccumulatorMeaning q pairValue (SignatureHeadPrepare.result a kr sr W bits rows) ∧
      DenseWord q 852 tupleValue (SignatureHeadPrepare.result a kr sr W bits rows) ∧
      QueryMasterFrame a (SignatureHeadPrepare.result a kr sr W bits rows) ∧
      WordBound B (SignatureHeadPrepare.result a kr sr W bits rows) ∧
      steps+1≤100*B+200 ∧
      QueryExecution.PrefixBound SignatureHeadPrepare.command (steps+1) a (996*B+200) := by
  obtain ⟨steps,ht,kr,sr,he,_,hb,_⟩ :=
    SignatureHeadPrepare.run a W bits rows B hW hbits hrows hrowlen hlen hkey hselect ha
  have hf:=prepared_masterFrame a kr sr W bits rows hW hbits hrows
  refine ⟨steps,kr,sr,he,hr.frame hf,?_,?_,hf,hb,ht,?_⟩
  · exact hm.frame (SignatureHeadPrepare.result_frame a kr sr W bits rows hW hbits hrows
      851 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hv.frame (SignatureHeadPrepare.result_frame a kr sr W bits rows hW hbits hrows
      852 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact (QueryExecution.prefix_local SignatureHeadPrepare.command (steps+1) B a ha).mono (by omega)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
