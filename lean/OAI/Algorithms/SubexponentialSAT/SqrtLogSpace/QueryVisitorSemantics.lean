import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryRepresentativeFold
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleWords

/-! Concrete execution of the two representative passes. The saved frame
stack is traversed in place, and every semantic dictionary is the one written
by the actual arithmetic command. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SubexpSetupStorage LeafHeadSetupProgram
open SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SignatureTupleSource
abbrev Data := State 40 896

/-- The mask produced by the actual addressed head loader. -/
def mask (s : ProducedSource) (z : ℕ) : List Bool :=
  List.ofFn (fun v : Fin s.input.n =>
    HeadIdentifierProgram.predicate s.input.rows s.input.low z v.val)

def baselineCost (s : ProducedSource) (B : ℕ) : ℕ :=
  QueryVisitorLoad.runEnvelope s.bound B+90*B+89

private theorem baselinePrefix_le (s : ProducedSource) (B : ℕ) :
    max (896*B+baselineCost s B) (914*B+18) ≤
      2400*(B+1)+baselineCost s B := by
  apply max_le
  · omega
  · omega

/-- One first-pass visit reloads the real head, then installs its parsed
representative in the ambient baseline. No head-mask producer is assumed. -/
theorem baseline_head {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P B : ℕ}
    {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (s : ProducedSource) (z : ℕ)
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
    (hv : DenseWord q 852 tupleValue a) (ha : WordBound B a)
    (hs : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 843=unary z) (htmp : a.stacks 841=[])
    (hword : (a.stacks 838).length=(selectedHeads s.input.n s.input.rows s.input.low z).length)
    (hbase : (a.stacks 869).length=s.input.n)
    (hcap : SignatureHeadLoader.retainedOutputBound s.input.n s.input.N s.input.D
      s.input.columnLength s.bound ≤ B) :
    ∃ steps b, Eval QueryVisitorProgram.baselineHead steps a b ∧
      QueryReady q node H high E U P b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 tupleValue b ∧ QueryMasterFrame a b ∧ WordBound B b ∧
      b.stacks 869=LeafAssignmentMergeProgram.merge
        (HighIncidenceProgram.Restriction.zeroMerge (mask s z) (a.stacks 838))
        (mask s z) (a.stacks 869) ∧ (b.stacks 869).length=s.input.n ∧
      (∀ i : Fin 896,768 ≤ i.val →
        i∉([846,847,859,869,872,873,874,875,876,877] : List (Fin 896)) →
        b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      steps ≤ baselineCost s B ∧
      QueryExecution.PrefixBound QueryVisitorProgram.baselineHead steps a (896*B+baselineCost s B) := by
  have hW : (a.stacks 141).length ≤ s.bound := by
    rw [s.source_offset a hs]
    exact s.bounded 141
  obtain ⟨rp,rm,rs,raw,shifted,nl,hl,hcl,hbl,_,_,_⟩ :=
    QueryVisitorLoad.load_run_polynomial s.input s.source s.ready s.bound s.bounded s.rows
      s.addressRegisters s.dimensionRegisters s.cacheRegisters s.cacheWords s.cache
      a hs z B s.bound hz ha hW hcap
  let loaded:=QueryVisitorLoad.result s.input z a rp rm rs raw shifted
  have hfl : QueryMasterFrame a loaded := QueryVisitorLoad.result_query_master_frame ..
  have hhigh (i : Fin 896) (hi : 768 ≤ i.val) (hne : i∉([846,847] : List (Fin 896))) :
      loaded.stacks i=a.stacks i :=
    QueryVisitorLoad.result_high_frame s.input z a rp rm rs raw shifted i hi hne
  have hmask : loaded.stacks 670=mask s z := QueryVisitorLoad.result_mask_word ..
  have hcount : HighIncidenceProgram.Restriction.highCount (loaded.stacks 670)=
      (selectedHeads s.input.n s.input.rows s.input.low z).length :=
    QueryVisitorLoad.result_mask_count ..
  have hword' : (loaded.stacks 838).length=
      HighIncidenceProgram.Restriction.highCount (loaded.stacks 670) := by
    rw [hhigh 838 (by decide) (by decide),hcount]
    exact hword
  have hbase' : (loaded.stacks 670).length=(loaded.stacks 869).length := by
    rw [QueryVisitorLoad.result_mask_length,hhigh 869 (by decide) (by decide),hbase]
  obtain ⟨ni,ri,hi,hri,hmi,hvi,hfi,hbi,hbaseline,hregs,hci,_⟩ :=
    QueryVisitorProgram.install_run (hr.frame hfl)
      (hm.frame (hhigh 851 (by decide) (by decide)))
      (hv.frame (hhigh 852 (by decide) (by decide))) hbl
      ((hhigh 841 (by decide) (by decide)).trans htmp) hword' hbase'
  have he : Eval QueryVisitorProgram.baselineHead (nl+ni) a (installedRepresentative loaded ri) :=
    hl.seq hi
  have hc : nl+ni ≤ baselineCost s B := by unfold baselineCost; omega
  refine ⟨nl+ni,_,he,hri,hmi,hvi,hfl.trans hfi,hbi,?_,?_,?_,?_,hc,?_⟩
  · simpa only [hmask,hhigh 838 (by decide) (by decide),hhigh 869 (by decide) (by decide)] using hbaseline
  · rw [hbaseline,LeafAssignmentMergeProgram.merge_length,
      QueryRepresentativeFold.zeroMerge_length,QueryVisitorLoad.result_mask_length]
  · intro i hi' hnot
    have hload : i∉([846,847] : List (Fin 896)) := by
      intro hm
      rcases List.mem_cons.mp hm with hh | hh
      · exact hnot (List.mem_cons.mpr (Or.inl hh))
      · exact hnot (List.mem_cons.mpr (Or.inr
          (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hh)))))
    have hinstall : i∉([145,859,869,872,873,874,875,876,877] : List (Fin 896)) := by
      have h145 : i≠145 := by
        intro hh
        subst i
        change 768 ≤ (145 : ℕ) at hi'
        omega
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hnot ⊢
      exact ⟨h145,hnot.2.2⟩
    exact (installedRepresentative_frame loaded ri i hinstall).trans (hhigh i hi' hload)
  · intro i hi'
    exact (hregs i hi').trans (QueryVisitorLoad.result_register_frame s.input z a rp rm rs raw shifted i hi')
  · exact (QueryExecution.prefix_local QueryVisitorProgram.baselineHead _ B a ha).mono (by omega)

/-- The whole first pass runs only the concrete addressed loader and overlay.
The list indexes the already emitted polynomial frame stack; no executable
assignment list or callback service occurs in this statement. -/
theorem baseline_pass {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P B : ℕ}
    {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (s : ProducedSource) (base : ℕ) (words : List (List Bool))
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
    (hv : DenseWord q 852 tupleValue a) (ha : WordBound B a)
    (hs : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hreps : a.stacks 837=suspendedFrames words)
    (haddress : a.stacks 845=unary (base+words.length))
    (hcurrent : a.stacks 838=[]) (hscratch : a.stacks 841=[])
    (hbase : (a.stacks 869).length=s.input.n)
    (hshape : ∀ pre word rest,words=pre++word::rest →
      word.length=(selectedHeads s.input.n s.input.rows s.input.low (base+rest.length)).length)
    (hcap : SignatureHeadLoader.retainedOutputBound s.input.n s.input.N s.input.D
      s.input.columnLength s.bound ≤ B) :
    ∃ steps b, Eval (QueryExecution.replay QueryVisitorProgram.baselineHead) steps a b ∧
      QueryReady q node H high E U P b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 tupleValue b ∧ QueryMasterFrame a b ∧ WordBound B b ∧
      FrameCursor base [] b ∧ b.stacks 841=[] ∧
      b.stacks 869=QueryRepresentativeFold.run (mask s) base words (a.stacks 869) ∧
      (b.stacks 869).length=s.input.n ∧
      (∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      steps+1 ≤ 18*B+8*(words.map List.length).sum+(baselineCost s B+10)*words.length+19 ∧
      QueryExecution.PrefixBound (QueryExecution.replay QueryVisitorProgram.baselineHead)
        (steps+1) a (max (896*B+baselineCost s B) (914*B+18)) := by
  let target:=QueryRepresentativeFold.run (mask s) base words (a.stacks 869)
  let I : List (List Bool) → Data → Prop := fun rest b =>
    QueryReady q node H high E U P b ∧ PairAccumulatorMeaning q pairValue b ∧
    DenseWord q 852 tupleValue b ∧ QueryMasterFrame a b ∧
    (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
    (∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i) ∧
    b.stacks 841=[] ∧ (b.stacks 869).length=s.input.n ∧
    QueryRepresentativeFold.run (mask s) base rest (b.stacks 869)=target ∧
    ∀ pre word tail,rest=pre++word::tail →
      word.length=(selectedHeads s.input.n s.input.rows s.input.low (base+tail.length)).length
  have step : ∀ word rest c,FrameCursor base (word::rest) c → I (word::rest) c →
      WordBound B c → ∃ steps b,
      Eval QueryVisitorProgram.baselineHead steps
        (headState c word (suspendedFrames rest) (unary (base+rest.length))) b ∧
      steps ≤ baselineCost s B ∧ b.stacks 838=word ∧ b.stacks 840=suspendedFrames rest ∧
      b.stacks 843=unary (base+rest.length) ∧ I rest (finished b) ∧ WordBound B b ∧
      QueryExecution.PrefixBound QueryVisitorProgram.baselineHead steps
        (headState c word (suspendedFrames rest) (unary (base+rest.length)))
        (896*B+baselineCost s B) := by
    intro word rest c hcursor hI hc
    rcases hI with ⟨hqr,hqm,hqv,hqf,hreg,hports,htmp,hlen,hvalue,hshapes⟩
    let parsed:=headState c word (suspendedFrames rest) (unary (base+rest.length))
    have hpf : QueryMasterFrame c parsed:=QueryVisitorProgram.headState_masterFrame ..
    have hparsed:=QueryVisitorProgram.readHead_state_bound hcursor hc
    have hwords:=headState_words c word (suspendedFrames rest) (unary (base+rest.length))
    have hparseFrame (i : Fin 896) (h838 : i≠838) (h840 : i≠840) (h843 : i≠843) :
        parsed.stacks i=c.stacks i :=
      headState_frame c word (suspendedFrames rest) (unary (base+rest.length)) i h838 h840 h843
    have hnative:=source_frame_of_queryFrame s.masters a parsed hs (hqf.trans hpf)
    obtain ⟨nt,b,he,hbr,hbm,hbv,hbf,hbb,hbaseline,hblen,hbframe,hbregs,ht,hprefix⟩ :=
      baseline_head s (base+rest.length) (hqr.frame hpf)
        (hqm.frame (hparseFrame 851 (by decide) (by decide) (by decide)))
        (hqv.frame (hparseFrame 852 (by decide) (by decide) (by decide))) hparsed hnative
        hwords.2.2 ((hparseFrame 841 (by decide) (by decide) (by decide)).trans htmp)
        (by rw [hwords.1]; exact hshapes [] word rest rfl)
        (by rw [hparseFrame 869 (by decide) (by decide) (by decide)]; exact hlen) hcap
    have hfinish:=QueryVisitorProgram.finishHead_masterFrame b
    have hfinished (i : Fin 896) (hi : i≠838) : (finished b).stacks i=b.stacks i := by
      rw [finished_stacks,Function.update_of_ne hi]
    refine ⟨nt,b,he,ht,?_,?_,?_,?_,hbb,hprefix⟩
    · exact (hbframe 838 (by decide) (by decide)).trans hwords.1
    · exact (hbframe 840 (by decide) (by decide)).trans hwords.2.1
    · exact (hbframe 843 (by decide) (by decide)).trans hwords.2.2
    · refine ⟨hbr.frame hfinish,hbm.frame (hfinished 851 (by decide)),
        hbv.frame (hfinished 852 (by decide)),hqf.trans (hpf.trans (hbf.trans hfinish)),
        ?_,?_,?_,?_,?_,?_⟩
      · intro i hi
        have hpreg:=CommandRegisterFrames.eval_register_frame
          (readHead_frames c word rest base hcursor.frames hcursor.current hcursor.address) i
          (QueryVisitorFrames.readHead_not_mem_writes i hi)
        have hfreg:=CommandRegisterFrames.eval_register_frame (finishHead_eval b) i
          (QueryVisitorFrames.finishHead_not_mem_writes i hi)
        exact hfreg.trans ((hbregs i hi).trans (hpreg.trans (hreg i hi)))
      · intro i hi
        have hn : i≠838 ∧ i≠840 ∧ i≠843 ∧ 768 ≤ i.val ∧
            i∉([846,847,859,869,872,873,874,875,876,877] : List (Fin 896)) := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl|rfl|rfl|rfl
          all_goals decide
        exact (hfinished i hn.1).trans ((hbframe i hn.2.2.2.1 hn.2.2.2.2).trans
          ((hparseFrame i hn.1 hn.2.1 hn.2.2.1).trans (hports i hi)))
      · exact (hfinished 841 (by decide)).trans ((hbframe 841 (by decide) (by decide)).trans
          ((hparseFrame 841 (by decide) (by decide) (by decide)).trans htmp))
      · simpa only [hfinished 869 (by decide)] using hblen
      · rw [hfinished 869 (by decide),hbaseline,hwords.1,
          hparseFrame 869 (by decide) (by decide) (by decide)]
        exact hvalue
      · intro pre next tail htail
        apply hshapes (word::pre) next tail
        simp only [List.cons_append,htail]
  have hstartFrame:=replay_masterFrame a
  have hstart (i : Fin 896) (h840 : i≠840) (h843 : i≠843) :
      (tested (restartState a)).stacks i=a.stacks i := restartState_frame a i h840 h843
  have hI : I words (tested (restartState a)) := by
    refine ⟨hr.frame hstartFrame,hm.frame (hstart 851 (by decide) (by decide)),
      hv.frame (hstart 852 (by decide) (by decide)),hstartFrame,?_,?_,?_,?_,?_,hshape⟩
    · intro i hi
      have hn0 : i≠0 := by intro hh; subst i; simp at hi
      have hn1 : i≠1 := by intro hh; subst i; simp at hi
      have hh:=CommandRegisterFrames.eval_register_frame (restart_eval a hscratch) i
        (QueryVisitorFrames.restart_not_mem_writes i hi)
      exact (StackRoutines.readRegs_frame _ _ _ _ _ hn0 hn1).trans hh
    · intro i hi
      have hn : i≠840 ∧ i≠843 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl
        all_goals decide
      exact hstart i hn.1 hn.2
    · exact (hstart 841 (by decide) (by decide)).trans hscratch
    · simpa only [hstart 869 (by decide) (by decide)] using hbase
    · rw [hstart 869 (by decide) (by decide)]
  obtain ⟨steps,b,he,hcursor,hI,hb,ht,hprefix⟩ :=
    QueryExecution.replay_resources QueryVisitorProgram.baselineHead base (baselineCost s B) B
      (896*B+baselineCost s B) I step words a hreps haddress hcurrent hscratch hI ha
  rcases hI with ⟨hbr,hbm,hbv,hbf,hregs,hports,htmp,hlen,hvalue,_⟩
  exact ⟨steps,b,he,hbr,hbm,hbv,hbf,hb,hcursor,htmp,hvalue,hlen,hports,hregs,ht,hprefix⟩


/-- The stored representative frames already pay for the parser's payload
mass; the proof does not construct any assignment enumeration. -/
theorem frame_word_mass (words : List (List Bool)) :
    (words.map List.length).sum ≤ (suspendedFrames words).length := by
  induction words with
  | nil => simp [suspendedFrames]
  | cons word rest ih =>
    simp only [List.map_cons,List.sum_cons,suspendedFrames,List.flatMap_cons,
      List.length_append,Encoding.length_frame,List.length_reverse] at *
    omega

/-- The actual initialization and whole first pass construct the full
ambient representative assignment. Its head masks and representative bits
are tied to the concrete loaded source, rather than supplied by an evaluator. -/
theorem initialize_baseline {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d}
    {node : Fin Q} {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {P B : ℕ} {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    (s : ProducedSource) (base : ℕ) (hn : s.input.n=n)
    (head : Fin n → Fin r)
    (reps : ∀ g, Moments.Head (fun v : ResidualEmbedding.Free H => head v.val) g → Bool)
    (words : Fin r → List Bool) (current : Fin r → Fin n → Bool)
    (hmask : ∀ g : Fin r,mask s (base+g.val)=
      List.ofFn (fun v : Fin n => decide (v∉H ∧ head v=g)))
    (hwords : ∀ g : Fin r,words g=HighIncidenceProgram.Restriction.selected true
      (mask s (base+g.val)) (List.ofFn (current g)))
    (hcurrentValue : ∀ g (v : Fin n) (hv : v∉H) (hg : head v=g),
      current g v=reps g ⟨⟨v,hv⟩,hg⟩)
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
    (ha : WordBound B a) (hPB : 4*P+6 ≤ B)
    (hs : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hreps : a.stacks 837=suspendedFrames (List.ofFn words).reverse)
    (haddress : a.stacks 845=unary (base+r)) (hcurrent : a.stacks 838=[])
    (hcap : SignatureHeadLoader.retainedOutputBound s.input.n s.input.N s.input.D
      s.input.columnLength s.bound ≤ B) :
    ∃ steps b, Eval (.seq QueryTupleInit.command
        (QueryExecution.replay QueryVisitorProgram.baselineHead)) steps a b ∧
      QueryReady q node H high E U P b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 1 b ∧ QueryMasterFrame a b ∧ WordBound B b ∧
      FrameCursor base [] b ∧ b.stacks 841=[] ∧
      b.stacks 869=List.ofFn (HighIncidence.glue H high
        (Moments.assemble (fun v : ResidualEmbedding.Free H => head v.val) reps)) ∧
      (∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      steps ≤ 1600*(B+1)+(baselineCost s B+10)*r ∧
      QueryExecution.PrefixBound (.seq QueryTupleInit.command
        (QueryExecution.replay QueryVisitorProgram.baselineHead)) steps a
        (2400*(B+1)+baselineCost s B) := by
  obtain ⟨ni,c,hi,hcr,hcm,hinit,hcb,hci,entries,he,hg,hv⟩ :=
    QueryTupleState.initialize_run hr hm ha hPB
  have hcv : DenseWord q 852 1 c := ⟨entries,he,hg,hv⟩
  have hcf := initialized_masterFrame hinit
  have hnative := source_frame_of_queryFrame s.masters a c hs hcf
  have hbaseline : c.stacks 869=List.ofFn
      (HighIncidence.glue H high (fun _ => false)) := hinit.baseline.trans hr.highBits
  have hlen : (c.stacks 869).length=s.input.n := by rw [hbaseline,List.length_ofFn,hn]
  have hshape : ∀ pre word rest,(List.ofFn words).reverse=pre++word::rest →
      word.length=(selectedHeads s.input.n s.input.rows s.input.low (base+rest.length)).length := by
    intro pre word rest hsplit
    have hwlen (i : Fin r) : (words i).length=
        HighIncidenceProgram.Restriction.highCount (mask s (base+i.val)) := by
      rw [hwords i]
      apply HighIncidenceProgram.Restriction.selected_true_length
      rw [hmask i,List.length_ofFn,List.length_ofFn]
    have hh:=QueryRepresentativeFold.reversed_word_shape (mask s) base words hwlen pre word rest hsplit
    exact hh.trans (HeadRepresentativeSemantics.headOrder_highCount _ _)
  obtain ⟨np,b,hp,hbr,hbm,hbv,hbf,hbb,hcursor,htmp,hvalue,_,hports,hregs,hcp,hprefix⟩ :=
    baseline_pass s base (List.ofFn words).reverse hcr hcm hcv hcb hnative
      ((hinit.frame 837 (by decide)).trans hreps)
      (by simpa only [List.length_reverse,List.length_ofFn] using
        (hinit.frame 845 (by decide)).trans haddress)
      ((hinit.frame 838 (by decide)).trans hcurrent) hinit.scratch hlen hshape hcap
  have hmass : ((List.ofFn words).reverse.map List.length).sum ≤ B :=
    (frame_word_mass _).trans (by rw [← hreps];exact ha 837)
  have htime : ni+np ≤ 1600*(B+1)+(baselineCost s B+10)*r := by
    simp only [List.length_reverse,List.length_ofFn] at hcp
    omega
  refine ⟨ni+np,b,hi.seq hp,hbr,hbm,hbv,hcf.trans hbf,hbb,hcursor,htmp,?_,?_,?_,htime,?_⟩
  · rw [hvalue,hbaseline]
    exact QueryRepresentativeFold.representative_words (mask s) base H high head reps words
      current hmask hwords hcurrentValue
  · intro i hi'
    have hchanged : i∉QueryTupleInit.changed := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi'
      rcases hi' with rfl|rfl|rfl|rfl
      all_goals decide
    exact (hports i hi').trans (hinit.frame i hchanged)
  · intro i hi'
    exact (hregs i hi').trans (QueryTupleInit.command_register_frame hi i hi')
  · apply QueryExecution.prefix_seq hi hp
    · exact (QueryExecution.prefix_local QueryTupleInit.command ni B a ha).mono (by omega)
    · exact (hprefix.monoSteps (Nat.le_succ np)).mono (baselinePrefix_le s B)


section Product
open scoped BigOperators
variable {R : Type*} [CommMonoid R] {r : ℕ}

/-- Proof-level product of the heads that the decreasing replay has not yet
visited. This indexes only the already emitted tuple. -/
def headPrefix (value : Fin r → R) (remaining : ℕ) : R :=
  ∏ g ∈ Finset.univ.filter (fun g : Fin r => g.val<remaining),value g

@[simp] theorem headPrefix_zero (value : Fin r → R) : headPrefix value 0=1 := by
  simp [headPrefix]

@[simp] theorem headPrefix_full (value : Fin r → R) : headPrefix value r=∏ g,value g := by
  simp [headPrefix]

theorem headPrefix_succ (value : Fin r → R) (remaining : ℕ) (h : remaining<r) :
    headPrefix value (remaining+1)=value ⟨remaining,h⟩*headPrefix value remaining := by
  have hs : Finset.univ.filter (fun g : Fin r => g.val<remaining+1)=
      insert ⟨remaining,h⟩ (Finset.univ.filter (fun g : Fin r => g.val<remaining)) := by
    ext g
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
    constructor
    · intro hg
      by_cases he : g.val=remaining
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (by omega)
    · intro hg
      rcases hg with hg|hg
      · subst g
        exact Nat.lt_succ_self _
      · omega
  unfold headPrefix
  rw [hs,Finset.prod_insert]
  simp

/-- Multiplying the visited head removes exactly its factor from the
unvisited product, without taking any quotient or applying readout early. -/
theorem headPrefix_step (value : Fin r → R) (remaining : ℕ) (h : remaining<r) (acc : R) :
    (acc*value ⟨remaining,h⟩)*headPrefix value remaining=
      acc*headPrefix value (remaining+1) := by
  rw [headPrefix_succ]
  exact mul_assoc _ _ _

end Product


open scoped BigOperators

def evaluationCost (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (P S Z B height : ℕ) : ℕ :=
  QueryVisitorHead.timeCoefficient q s.bound P S Z B*2^height

def evaluationSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (P B : ℕ) : ℕ :=
  max (QueryVisitorLoad.runEnvelope s.bound P)
    (max (996*P+200) (max B (896*P+QueryVisitorHead.multiplyBudget q P)))

/-- The fixed second replay multiplies the actual normalized head sums in
reverse head order. The proof tracks the remaining product without division;
readout is still deferred to the completed tuple tail. -/
theorem evaluation_pass (s : ProducedSource) {d M P S Z B width height : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M P S Z B s.bound width)
    (reps : ∀ g, Moments.Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g → Bool)
    (hbalanced : ∀ g : Fin s.input.r,
      HeadIdentifierProgram.count (HeadIdentifierProgram.predicate s.input.rows s.input.low
        (s.base+g.val)) s.input.n ≤ height)
    (a : Data)
    {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {initial : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hr : QueryReady q s.input.node H high E U M a)
    (hm : PairAccumulatorMeaning q pairValue a)
    (hv : DenseWord q 852 initial a) (ha : WordBound P a)
    (hs : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hreps : a.stacks 837=suspendedFrames (List.ofFn (fun g =>
      QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g reps)).reverse)
    (haddress : a.stacks 845=unary (s.base+s.input.r))
    (hcurrent : a.stacks 838=[]) (hscratch : a.stacks 841=[])
    (hbaseline : a.stacks 869=List.ofFn (HighIncidence.glue H high
      (Moments.assemble (fun v : ResidualEmbedding.Free H => head s.input.node v.val) reps))) :
    ∃ steps b, Eval (QueryExecution.replay QueryVisitorProgram.evaluateHead) steps a b ∧
      QueryReady q s.input.node H high E U M b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 (initial*∏ g : Fin s.input.r,
        QueryVisitorHead.headValue q s.input.node H E U high owner head g reps
          (QueryVisitorHead.factorIds s.input g)) b ∧
      QueryMasterFrame a b ∧ WordBound P b ∧ FrameCursor s.base [] b ∧ b.stacks 841=[] ∧
      b.stacks 869=a.stacks 869 ∧
      (∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      steps+1 ≤ 26*P+(evaluationCost s q P S Z B height+10)*s.input.r+19 ∧
      QueryExecution.PrefixBound (QueryExecution.replay QueryVisitorProgram.evaluateHead)
        (steps+1) a (max (evaluationSpace s q P B) (914*P+18)) := by
  let words := (List.ofFn (fun g =>
    QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g reps)).reverse
  let value := fun g : Fin s.input.r =>
    QueryVisitorHead.headValue q s.input.node H E U high owner head g reps
      (QueryVisitorHead.factorIds s.input g)
  let target := initial*∏ g,value g
  let I : List (List Bool) → Data → Prop := fun rest c =>
    QueryReady q s.input.node H high E U M c ∧ PairAccumulatorMeaning q pairValue c ∧
    QueryMasterFrame a c ∧ (∀ i : Fin 40,16 ≤ i.val → c.regs i=a.regs i) ∧
    (∀ i∈([836,837,842,845] : List (Fin 896)),c.stacks i=a.stacks i) ∧
    c.stacks 841=[] ∧ c.stacks 869=a.stacks 869 ∧
    (∃ pre,words=pre++rest) ∧
    ∃ acc,DenseWord q 852 acc c ∧ acc*headPrefix value rest.length=target
  have step : ∀ word rest c,FrameCursor s.base (word::rest) c → I (word::rest) c →
      WordBound P c → ∃ steps b,
      Eval QueryVisitorProgram.evaluateHead steps
        (headState c word (suspendedFrames rest) (unary (s.base+rest.length))) b ∧
      steps ≤ evaluationCost s q P S Z B height ∧
      b.stacks 838=word ∧ b.stacks 840=suspendedFrames rest ∧
      b.stacks 843=unary (s.base+rest.length) ∧ I rest (finished b) ∧ WordBound P b ∧
      QueryExecution.PrefixBound QueryVisitorProgram.evaluateHead steps
        (headState c word (suspendedFrames rest) (unary (s.base+rest.length)))
        (evaluationSpace s q P B) := by
    intro word rest c hcursor hI hc
    rcases hI with ⟨hqr,hqm,hqf,hreg,hports,htmp,hbase,⟨pre,hpre⟩,acc,hacc,hprod⟩
    obtain ⟨g,hg,hgword⟩:=QueryRepresentativeFold.reverse_word_address
      (fun g => QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g reps)
      pre word rest hpre
    let parsed:=headState c word (suspendedFrames rest) (unary (s.base+rest.length))
    have hpf : QueryMasterFrame c parsed:=QueryVisitorProgram.headState_masterFrame ..
    have hparsed:=QueryVisitorProgram.readHead_state_bound hcursor hc
    have hwords:=headState_words c word (suspendedFrames rest) (unary (s.base+rest.length))
    have hparseFrame (i : Fin 896) (h838 : i≠838) (h840 : i≠840) (h843 : i≠843) :
        parsed.stacks i=c.stacks i :=
      headState_frame c word (suspendedFrames rest) (unary (s.base+rest.length)) i h838 h840 h843
    have hnative:=source_frame_of_queryFrame s.masters a parsed hs (hqf.trans hpf)
    have hW : (parsed.stacks 141).length ≤ s.bound := by
      rw [s.source_offset parsed hnative]
      exact s.bounded 141
    obtain ⟨nt,b,he,hbr,hbm,hbv,_,h841,hbf,hbb,hbframe,hbregs,ht,hprefix⟩ :=
      QueryVisitorHead.evaluateHead_run s.input q H E U high owner s.owner head facts caps g reps
        s.source s.ready s.bounded s.addressRegisters s.dimensionRegisters s.cacheRegisters
        s.cacheWords s.cache parsed hnative (hqr.frame hpf) hparsed
        (hqm.frame (hparseFrame 851 (by decide) (by decide) (by decide)))
        (hacc.frame (hparseFrame 852 (by decide) (by decide) (by decide)))
        ((hparseFrame 869 (by decide) (by decide) (by decide)).trans (hbase.trans hbaseline))
        (hwords.1.trans hgword.symm)
        (by simpa only [parsed,hg,ProducedSource.base] using hwords.2.2) hW
    have hfinish:=QueryVisitorProgram.finishHead_masterFrame b
    have hfinished (i : Fin 896) (hi : i≠838) : (finished b).stacks i=b.stacks i := by
      rw [finished_stacks,Function.update_of_ne hi]
    have hcost : nt ≤ evaluationCost s q P S Z B height :=
      ht.trans (QueryVisitorHead.time_le_max_head q s.bound P S Z B _ height
        (HeadIdentifierProgram.count_le _ _) (hbalanced g))
    refine ⟨nt,b,he,hcost,?_,?_,?_,?_,hbb,hprefix⟩
    · exact (hbframe 838 (by decide)).trans hwords.1
    · exact (hbframe 840 (by decide)).trans hwords.2.1
    · exact (hbframe 843 (by decide)).trans hwords.2.2
    · refine ⟨hbr.frame hfinish,hbm.frame (hfinished 851 (by decide)),
        hqf.trans (hpf.trans (hbf.trans hfinish)),?_,?_,
        (hfinished 841 (by decide)).trans h841,?_,?_,acc*value g,
        hbv.frame (hfinished 852 (by decide)),?_⟩
      · intro i hi
        have hpreg:=CommandRegisterFrames.eval_register_frame
          (readHead_frames c word rest s.base hcursor.frames hcursor.current hcursor.address) i
          (QueryVisitorFrames.readHead_not_mem_writes i hi)
        have hfreg:=CommandRegisterFrames.eval_register_frame (finishHead_eval b) i
          (QueryVisitorFrames.finishHead_not_mem_writes i hi)
        exact hfreg.trans ((hbregs i hi).trans (hpreg.trans (hreg i hi)))
      · intro i hi
        have hn : i≠838 ∧ i≠840 ∧ i≠843 ∧ i∈QueryVisitorHead.visitorPorts := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl|rfl|rfl|rfl
          all_goals decide
        exact (hfinished i hn.1).trans ((hbframe i hn.2.2.2).trans
          ((hparseFrame i hn.1 hn.2.1 hn.2.2.1).trans (hports i hi)))
      · exact (hfinished 869 (by decide)).trans ((hbframe 869 (by decide)).trans
          ((hparseFrame 869 (by decide) (by decide) (by decide)).trans hbase))
      · exact ⟨pre++[word],by simpa only [List.append_assoc,List.singleton_append] using hpre⟩
      · have hrest : rest.length<s.input.r := by rw [←hg];exact g.isLt
        have hgeq : g=⟨rest.length,hrest⟩ := Fin.ext hg
        rw [hgeq,headPrefix_step]
        simpa only [List.length_cons] using hprod
  have hstartFrame:=replay_masterFrame a
  have hstart (i : Fin 896) (h840 : i≠840) (h843 : i≠843) :
      (tested (restartState a)).stacks i=a.stacks i := restartState_frame a i h840 h843
  have hI : I words (tested (restartState a)) := by
    refine ⟨hr.frame hstartFrame,hm.frame (hstart 851 (by decide) (by decide)),hstartFrame,
      ?_,?_,(hstart 841 (by decide) (by decide)).trans hscratch,
      hstart 869 (by decide) (by decide),⟨[],rfl⟩,initial,
      hv.frame (hstart 852 (by decide) (by decide)),?_⟩
    · intro i hi
      have hn0 : i≠0 := by intro hh; subst i; simp at hi
      have hn1 : i≠1 := by intro hh; subst i; simp at hi
      have hh:=CommandRegisterFrames.eval_register_frame (restart_eval a hscratch) i
        (QueryVisitorFrames.restart_not_mem_writes i hi)
      exact (StackRoutines.readRegs_frame _ _ _ _ _ hn0 hn1).trans hh
    · intro i hi
      have hn : i≠840 ∧ i≠843 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl
        all_goals decide
      exact hstart i hn.1 hn.2
    · simp only [words,List.length_reverse,List.length_ofFn,headPrefix_full,target]
  obtain ⟨steps,b,he,hcursor,hI,hb,ht,hprefix⟩ :=
    QueryExecution.replay_resources QueryVisitorProgram.evaluateHead s.base
      (evaluationCost s q P S Z B height) P (evaluationSpace s q P B)
      I step words a hreps
      (by simpa only [words,List.length_reverse,List.length_ofFn] using haddress)
      hcurrent hscratch hI ha
  rcases hI with ⟨hbr,hbm,hbf,hregs,hports,htmp,hbase,_,acc,hacc,hprod⟩
  have hav : acc=target := by simpa only [List.length_nil,headPrefix_zero,mul_one] using hprod
  have hmass : (words.map List.length).sum ≤ P :=
    (frame_word_mass _).trans (by rw [←hreps];exact ha 837)
  refine ⟨steps,b,he,hbr,hbm,?_,hbf,hb,hcursor,htmp,hbase,hports,hregs,?_,hprefix⟩
  · simpa only [hav,target,value] using hacc
  · simp only [words,List.length_reverse,List.length_ofFn] at ht
    dsimp only [words] at hmass
    omega


/-- The literal source certificate identifies the actual mask emitted at each
address with the original free head fiber. -/
theorem facts_mask (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head) (g : Fin s.input.r) :
    mask s (s.base+g.val)=
      List.ofFn (fun v : Fin s.input.n => decide (v∉H ∧ head s.input.node v=g)) := by
  apply congrArg List.ofFn
  funext v
  apply Bool.eq_iff_iff.mpr
  have hv : v.val<s.input.n := v.isLt
  simpa only [ProducedSource.base,HeadIdentifierProgram.chosenIds,List.mem_filter,List.mem_range,
    hv,true_and,decide_eq_true_eq,exists_prop] using facts.selected g v

/-- The same physical representative word used by the key evaluator is the
selected ambient extension used by the first pass. -/
theorem representativeWord_selected (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head) (g : Fin s.input.r)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) k → Bool) :
    QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g reps=
      HighIncidenceProgram.Restriction.selected true (mask s (s.base+g.val))
        (List.ofFn (SignatureTupleWords.ambientAssignment H (head s.input.node) g (reps g))) := by
  let p := HeadIdentifierProgram.predicate s.input.rows s.input.low (s.base+g.val)
  let e := BucketTupleProgram.Concrete.freeAssignmentEquiv H
    (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g
    (HeadIdentifierProgram.chosenIds p s.input.n)
    (HeadIdentifierProgram.chosenIds_bound p s.input.n)
    (HeadIdentifierProgram.chosenIds_nodup p s.input.n) (facts.selected g)
  let candidate := (AttainedSignatures.assignmentEquiv
    (HeadIdentifierProgram.chosenIds p s.input.n).length).symm (e (reps g))
  have hw := SignatureTupleWords.emitted_word H (head s.input.node) g p
    (facts.selected g) candidate
  have hbits := AttainedSignatures.assignment_word
    (HeadIdentifierProgram.chosenIds p s.input.n).length candidate
  have he : AttainedSignatures.assignmentEquiv _ candidate=e (reps g) :=
    Equiv.apply_symm_apply _ _
  rw [he] at hbits hw
  have he' : e.symm (e (reps g))=reps g := e.symm_apply_apply _
  change _=HighIncidenceProgram.Restriction.selected true (mask s (s.base+g.val))
    (List.ofFn (SignatureTupleWords.ambientAssignment H (head s.input.node) g (e.symm (e (reps g))))) at hw
  rw [he'] at hw
  exact hbits.trans hw


def visitorCost (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (P S Z B height : ℕ) : ℕ :=
  QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J P+1600*(P+1)+
    (baselineCost s P+evaluationCost s q P S Z B height+20)*s.input.r

def visitorSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (P B : ℕ) : ℕ :=
  max (2400*(P+1)+baselineCost s P+
    QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J P)
    (evaluationSpace s q P B)

private theorem baselinePrefix_le_visitorSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (P B : ℕ) :
    max (896*P+baselineCost s P) (914*P+18) ≤ visitorSpace s q P B := by
  calc
    max (896*P+baselineCost s P) (914*P+18) ≤
        2400*(P+1)+baselineCost s P := baselinePrefix_le s P
    _ ≤ 2400*(P+1)+baselineCost s P+
        QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J P :=
      Nat.le_add_right _ _
    _ ≤ visitorSpace s q P B := Nat.le_max_left _ _

private theorem evaluationSpace_le_visitorSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (P B : ℕ) :
    evaluationSpace s q P B ≤ visitorSpace s q P B :=
  Nat.le_max_right _ _

private theorem evaluationPrefix_le_visitorSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (P B : ℕ) :
    max (evaluationSpace s q P B) (914*P+18) ≤ visitorSpace s q P B := by
  apply max_le
  · exact evaluationSpace_le_visitorSpace s q P B
  · exact (Nat.le_max_right (896*P+baselineCost s P) (914*P+18)).trans
      (baselinePrefix_le_visitorSpace s q P B)

private theorem initialPrefix_le_visitorSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (P B steps : ℕ)
    (hsteps : steps ≤ 1500*(P+1)) :
    896*P+steps ≤ visitorSpace s q P B := by
  calc
    896*P+steps ≤ 896*P+1500*(P+1) := Nat.add_le_add_left hsteps _
    _ ≤ 2400*(P+1) := by omega
    _ ≤ 2400*(P+1)+baselineCost s P := Nat.le_add_right _ _
    _ ≤ 2400*(P+1)+baselineCost s P+
        QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J P :=
      Nat.le_add_right _ _
    _ ≤ visitorSpace s q P B := Nat.le_max_left _ _

private theorem finishPrefix_le_visitorSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (P B steps : ℕ)
    (hsteps : steps+1 ≤
      QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J P+16*P+25) :
    896*P+steps ≤ visitorSpace s q P B := by
  let budget := QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J P
  have hstep : steps ≤ budget+16*P+25 := (Nat.le_succ steps).trans hsteps
  calc
    896*P+steps ≤ 896*P+(budget+16*P+25) := Nat.add_le_add_left hstep _
    _ = (912*P+25)+budget := by omega
    _ ≤ 2400*(P+1)+budget := Nat.add_le_add_right (by omega) _
    _ ≤ (2400*(P+1)+baselineCost s P)+budget :=
      Nat.add_le_add_right (Nat.le_add_right _ _) _
    _ ≤ visitorSpace s q P B := Nat.le_max_left _ _

/-- The actual fixed visitor first reconstructs every representative, then
multiplies every restricted head sum, and finally adds one completed readout.
All execution witnesses are produced by the concrete commands in this proof. -/
theorem visitor_run (s : ProducedSource) {d M P S Z B width height : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M P S Z B s.bound width)
    (reps : ∀ g, Moments.Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g → Bool)
    (hbalanced : ∀ g : Fin s.input.r,
      HeadIdentifierProgram.count (HeadIdentifierProgram.predicate s.input.rows s.input.low
        (s.base+g.val)) s.input.n ≤ height)
    (a : Data) {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    (hr : QueryReady q s.input.node H high E U M a)
    (hm : PairAccumulatorMeaning q pairValue a) (ha : WordBound P a)
    (hs : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hreps : a.stacks 837=suspendedFrames (List.ofFn (fun g =>
      QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g reps)).reverse)
    (haddress : a.stacks 845=unary (s.base+s.input.r)) (hcurrent : a.stacks 838=[]) :
    ∃ steps b, Eval QueryVisitorProgram.visitor steps a b ∧
      QueryReady q s.input.node H high E U M b ∧
      PairAccumulatorMeaning q (pairValue+Dense.readout (∏ g : Fin s.input.r,
        QueryVisitorHead.headValue q s.input.node H E U high owner head g reps
          (QueryVisitorHead.factorIds s.input g))) b ∧
      QueryMasterFrame a b ∧ WordBound P b ∧
      (∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      (∀ i∈SignatureTupleProgram.currentHeadPorts,b.stacks i=[]) ∧
      steps+1 ≤ visitorCost s q P S Z B height ∧
      QueryExecution.PrefixBound QueryVisitorProgram.visitor (steps+1) a (visitorSpace s q P B) := by
  let words := fun g => QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g reps
  let frameWords := (List.ofFn words).reverse
  obtain ⟨ni,a1,hi,hr1,hm1,hinit,hb1,hci,entries,hbytes,hgood,hunit⟩ :=
    QueryTupleState.initialize_run hr hm ha caps.cache
  have hv1 : DenseWord q 852 1 a1 := ⟨entries,hbytes,hgood,hunit⟩
  have hf1:=initialized_masterFrame hinit
  have hs1:=source_frame_of_queryFrame s.masters a a1 hs hf1
  have hbaseline1 : a1.stacks 869=List.ofFn
      (HighIncidence.glue H high (fun _ => false)) := hinit.baseline.trans hr.highBits
  have hlen1 : (a1.stacks 869).length=s.input.n := by rw [hbaseline1,List.length_ofFn]
  have hshape : ∀ pre word rest,frameWords=pre++word::rest →
      word.length=(selectedHeads s.input.n s.input.rows s.input.low (s.base+rest.length)).length := by
    intro pre word rest hsplit
    obtain ⟨g,hg,he⟩:=QueryRepresentativeFold.reverse_word_address words pre word rest hsplit
    rw [←he]
    change (List.ofFn _).length=_
    rw [List.length_ofFn]
    change (HeadIdentifierProgram.chosenIds
      (HeadIdentifierProgram.predicate s.input.rows s.input.low (s.base+g.val)) s.input.n).length=_
    rw [hg]
    rfl
  obtain ⟨nb,a2,hbase,hr2,hm2,hv2,hf2,hb2,hcursor2,h841,hbaseline2,_,hports2,hregs2,hcb,hpb⟩ :=
    baseline_pass s s.base frameWords hr1 hm1 hv1 hb1 hs1
      ((hinit.frame 837 (by decide)).trans hreps)
      (by simpa only [frameWords,List.length_reverse,List.length_ofFn] using
        (hinit.frame 845 (by decide)).trans haddress)
      ((hinit.frame 838 (by decide)).trans hcurrent) hinit.scratch hlen1 hshape caps.load
  have hfullbase : a2.stacks 869=List.ofFn (HighIncidence.glue H high
      (Moments.assemble (fun v : ResidualEmbedding.Free H => head s.input.node v.val) reps)) := by
    rw [hbaseline2,hbaseline1]
    exact QueryRepresentativeFold.representative_words (mask s) s.base H high (head s.input.node)
      reps words (fun g => SignatureTupleWords.ambientAssignment H (head s.input.node) g (reps g))
      (facts_mask s q H owner head facts) (fun g => representativeWord_selected s q H owner head facts g reps)
      (fun g v hv hg => SignatureTupleWords.ambientAssignment_head H (head s.input.node) g (reps g) v hv hg)
  have hs2:=source_frame_of_queryFrame s.masters a1 a2 hs1 hf2
  have hreps2 : a2.stacks 837=suspendedFrames frameWords :=
    (hports2 837 (by decide)).trans ((hinit.frame 837 (by decide)).trans hreps)
  have haddress2 : a2.stacks 845=unary (s.base+s.input.r) :=
    (hports2 845 (by decide)).trans ((hinit.frame 845 (by decide)).trans haddress)
  obtain ⟨ne,a3,he,hr3,hm3,hv3,hf3,hb3,_,_,_,hports3,hregs3,hce,hpe⟩ :=
    evaluation_pass s q H E U high owner head facts caps reps hbalanced a2 hr2 hm2 hv2 hb2
      hs2 hreps2 haddress2 hcursor2.current h841 hfullbase
  obtain ⟨product,hprodBytes,hprodGood,hprodValue⟩:=hv3.entries
  obtain ⟨nf,b,hf,hrb,hmb,hbb,hff,hcurrentb,hframe,hregs,hcf⟩ :=
    QueryTupleState.finish hr3 hm3 product hprodGood hprodBytes hb3 caps.multiply
  have whole : Eval QueryVisitorProgram.visitor (ni+(nb+(ne+nf))) a b :=
    hi.seq (hbase.seq (he.seq hf))
  have hmass : (frameWords.map List.length).sum ≤ P :=
    (frame_word_mass _).trans (by rw [←hreps];exact ha 837)
  have htime : ni+(nb+(ne+nf))+1 ≤ visitorCost s q P S Z B height := by
    dsimp only [frameWords] at hmass
    simp only [frameWords,List.length_reverse,List.length_ofFn] at hcb
    unfold visitorCost
    have hd : (baselineCost s P+evaluationCost s q P S Z B height+20)*s.input.r =
        (baselineCost s P+10)*s.input.r+(evaluationCost s q P S Z B height+10)*s.input.r := by ring
    rw [hd]
    omega
  let D := visitorSpace s q P B
  have hpi : QueryExecution.PrefixBound QueryTupleInit.command ni a D :=
    (QueryExecution.prefix_local QueryTupleInit.command ni P a ha).mono
      (initialPrefix_le_visitorSpace s q P B ni hci)
  have hpb' : QueryExecution.PrefixBound (QueryExecution.replay QueryVisitorProgram.baselineHead) nb a1 D := by
    exact (hpb.monoSteps (Nat.le_succ nb)).mono (baselinePrefix_le_visitorSpace s q P B)
  have hpe' : QueryExecution.PrefixBound (QueryExecution.replay QueryVisitorProgram.evaluateHead) ne a2 D := by
    exact (hpe.monoSteps (Nat.le_succ ne)).mono (evaluationPrefix_le_visitorSpace s q P B)
  have hpf : QueryExecution.PrefixBound QueryExecution.TupleEnd.command nf a3 D :=
    (QueryExecution.prefix_local QueryExecution.TupleEnd.command nf P a3 hb3).mono
      (finishPrefix_le_visitorSpace s q P B nf hcf)
  have hpwhole:=QueryExecution.prefix_seq hi (hbase.seq (he.seq hf)) hpi
    (QueryExecution.prefix_seq hbase (he.seq hf) hpb' (QueryExecution.prefix_seq he hf hpe' hpf))
  refine ⟨_,b,whole,hrb,?_,hf1.trans (hf2.trans (hf3.trans hff)),hbb,?_,?_,hcurrentb,htime,?_⟩
  · simpa only [hprodValue,one_mul] using hmb
  · intro i hi'
    have hn : 128 ≤ i.val ∧ i∉currentHeadPorts ∧ i≠851 ∧ i≠852 ∧ i∉QueryTupleInit.changed := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi'
      rcases hi' with rfl|rfl|rfl|rfl
      all_goals decide
    exact (hframe i hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1).trans
      ((hports3 i hi').trans ((hports2 i hi').trans (hinit.frame i hn.2.2.2.2)))
  · intro i hi'
    exact (hregs i hi').trans ((hregs3 i hi').trans ((hregs2 i hi').trans
      (QueryTupleInit.command_register_frame hi i hi')))
  · constructor
    exact StructuredSpace.compiled_halt_stack_bound whole 838 838 hpwhole.bound


def visitorCoefficient (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (P S Z B : ℕ) : ℕ :=
  QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J P+1600*(P+1)+
    baselineCost s P+QueryVisitorHead.timeCoefficient q s.bound P S Z B+20

theorem visitorCost_le (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (P S Z B height : ℕ) :
    visitorCost s q P S Z B height ≤
      visitorCoefficient s q P S Z B*(s.input.r+1)*2^height := by
  have hp : 1 ≤ 2^height := one_le_pow₀ (by omega)
  let c := visitorCoefficient s q P S Z B
  have hbase : QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J P+
      1600*(P+1) ≤ c*2^height := by
    calc
      _ ≤ c := by dsimp [c,visitorCoefficient];omega
      _ ≤ c*2^height := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left c hp
  have hhead : baselineCost s P+evaluationCost s q P S Z B height+20 ≤ c*2^height := by
    unfold evaluationCost
    calc
      _ ≤ (baselineCost s P+QueryVisitorHead.timeCoefficient q s.bound P S Z B+20)*2^height := by
        nlinarith
      _ ≤ c*2^height := Nat.mul_le_mul_right _ (by dsimp [c,visitorCoefficient];omega)
  calc
    visitorCost s q P S Z B height ≤ c*2^height+(c*2^height)*s.input.r :=
      Nat.add_le_add hbase (Nat.mul_le_mul_right _ hhead)
    _ = visitorCoefficient s q P S Z B*(s.input.r+1)*2^height := by dsimp [c];ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
