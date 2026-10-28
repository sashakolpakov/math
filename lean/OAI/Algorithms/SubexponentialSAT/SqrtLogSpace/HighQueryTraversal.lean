import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop

/-! The actual fixed high-counter loop. The induction index and prefix sum
are proof data only; executable syntax retains one bounded-width odometer and
one binary accumulator. The concrete per-rank stream proof is supplied by the
downstream count integration, not by a runtime callback. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal

open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram
open HighQueryAdapter PreparedBranchCount HighQueryLoop
open ExecCNFTupleEnumeration ExecCNFTupleOdometer
open HashGreedyProgram.NativeRound

/-- Prefix composition for a tested loop, before specializing its fixed body. -/
theorem while_step_space {body : Cmd 40 896} {test : Fin 40} {nb nt D : ℕ}
    {a b c : HighQueryAdapter.Data} (flag : a.regs test=true)
    (hb : Eval body nb a b) (ht : Eval (.while test body) nt b c)
    (sb : StageSpace body nb a D) (st : StageSpace (.while test body) nt b D) :
    StageSpace (.while test body) (nb+nt+1) a D :=
  ⟨StructuredSpace.while_true_stack_bound flag hb ht 778 777 sb.bound st.bound
    _ _ _ (compiled_site _ 778 777)⟩

/-- The final false guard does not allocate stack words. -/
theorem while_done_space (body : Cmd 40 896) (test : Fin 40) (D : ℕ)
    (a : HighQueryAdapter.Data) (flag : a.regs test=false)
    (bound : ∀ i,(a.stacks i).length≤D) : StageSpace (.while test body) 1 a D :=
  ⟨StructuredSpace.while_false_stack_bound body test a flag bound
    _ _ _ (compiled_site _ 778 777)⟩

/-- At overflow the fixed-width physical odometer returns its unique zero
tuple, including the empty tuple when the high set is empty. -/
theorem overflow_counter {n : ℕ} (H : Finset (Fin n)) (words : List (List Bool))
    (shape : words.map List.length=List.replicate H.card 1)
    (last : CounterPrograms.value words.flatten+1=2^H.card) (a : HighQueryAdapter.Data) :
    (advanceResult highPorts.counter a words).stacks 789=
      Encoding.encodeList id (List.replicate H.card [false]) := by
  have hlast : CounterPrograms.value words.flatten+1=2^words.flatten.length := by
    rw [flattened_length H words shape]
    exact last
  have hz := (overflow_at_last words hlast).2
  have hzero : (bumpWords words).2=List.replicate H.card [false] := by
    apply tuple_eq_of_shape_value
    · simpa only [List.map_replicate,List.length_singleton] using
        (bumpWords_lengths words).trans shape
    · rw [hz]
      exact (zero_tuple_value H.card 1).symm
  change (advanceResult highPorts.counter a words).stacks highPorts.counter.counter=_
  rw [advanceResult_counter,hzero]

variable {n : ℕ} (H : Finset (Fin n))
  (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
  (clause : List (SAT.Literal (Fin n)))
  (I : HighQueryAdapter.Data → Prop) (B C D : ℕ)

/-- Direct induction over the remaining numerical ranks executes the fixed
branch and the real odometer, including the final overflow. Every boundary
returns the same B; intermediate prefixes use a separate uniform maximum.
The branch premise names the fixed actual command and remains explicit only
in this compositional support theorem. -/
theorem loop_run
    (stable : CounterForPrograms.FrameStable highPorts.counter (fun _ => I))
    (width : 4*H.card+1≤B) (BD : B≤D)
    (branch : ∀ (rank : ℕ), rank<2^H.card → ∀ (words : List (List Bool))
      (a : HighQueryAdapter.Data), words.map List.length=List.replicate H.card 1 → I a →
      a.stacks 789=Encoding.encodeList id words → a.stacks 790=[] →
      a.stacks 791=[] → a.regs 21=true → CounterPrograms.value words.flatten=rank →
      BinaryArithmetic.toNat (a.stacks 788)=rankSum (rankValue H hashes marked clause) 0 rank →
      (a.stacks 788).length≤n+1 → (∀ i,(a.stacks i).length≤B) →
      ∃ steps b, Eval HighQueryProgram.branch steps a b ∧ steps≤C ∧ I b ∧
        BinaryArithmetic.toNat (b.stacks 788)=
          rankSum (rankValue H hashes marked clause) 0 (rank+1) ∧
        (b.stacks 788).length≤n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
        b.stacks 789=a.stacks 789 ∧ b.stacks 790=a.stacks 790 ∧
        (∀ i,(b.stacks i).length≤B) ∧
        StageSpace HighQueryProgram.branch steps a D)
    (fuel : ℕ) : ∀ (rank : ℕ) (words : List (List Bool)) (a : HighQueryAdapter.Data),
      words.map List.length=List.replicate H.card 1 → I a →
      a.stacks 789=Encoding.encodeList id words → a.stacks 790=[] → a.stacks 791=[] →
      a.regs 21=true → CounterPrograms.value words.flatten=rank → rank+fuel=2^H.card →
      BinaryArithmetic.toNat (a.stacks 788)=rankSum (rankValue H hashes marked clause) 0 rank →
      (a.stacks 788).length≤n+1 → (∀ i,(a.stacks i).length≤B) →
      ∃ steps b, Eval (loopCmd highPorts.counter HighQueryProgram.branch) steps a b ∧
        steps≤fuel*(C+28*H.card+12)+1 ∧ I b ∧
        BinaryArithmetic.toNat (b.stacks 788)=fullCount hashes marked clause ∧
        (b.stacks 788).length≤n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
        b.stacks 789=Encoding.encodeList id (List.replicate H.card [false]) ∧
        b.stacks 790=[] ∧ b.regs 21=false ∧ (∀ i,(b.stacks i).length≤B) ∧
        StageSpace (loopCmd highPorts.counter HighQueryProgram.branch) steps a
          (max D (40*(H.card+1))) := by
  induction fuel with
  | zero =>
    intro rank words a shape hi hc hs ht hf hv hremaining hacc hlen hb
    have hlt := physical_rank_lt H words shape
    omega
  | succ fuel ih =>
    intro rank words a shape hi hc hs ht hf hv hremaining hacc hlen hb
    have hr : rank<2^H.card := by omega
    obtain ⟨nb,b,he,hnb,hbi,hba,hbl,hbout,hbt,hbc,hbs,hbb,hbp⟩ :=
      branch rank hr words a shape hi hc hs ht hf hv hacc hlen hb
    have hbc' : b.stacks 789=Encoding.encodeList id words := hbc.trans hc
    have hbs' : b.stacks 790=[] := hbs.trans hs
    obtain ⟨na,hna,ha,hdb,hdp⟩ := advance_resources H words shape b B hbc' hbs' width hbb
    let next := advanceResult highPorts.counter b words
    have hoff := advanceResult_outside highPorts.counter b words
    have hdi : I next := stable 0 b next hoff hbi
    have hda : BinaryArithmetic.toNat (next.stacks 788)=
        rankSum (rankValue H hashes marked clause) 0 (rank+1) := by
      rw [←hoff 788 (by decide) (by decide)]
      exact hba
    have hdl : (next.stacks 788).length≤n+1 := by
      rw [←hoff 788 (by decide) (by decide)]
      exact hbl
    have hdo : next.stacks 323=[] := by
      rw [←hoff 323 (by decide) (by decide)]
      exact hbout
    have hdt : next.stacks 791=[] := by
      rw [←hoff 791 (by decide) (by decide)]
      exact hbt
    have hds : next.stacks 790=[] := advanceResult_scratch highPorts.counter b words
    have hbody := he.seq ha
    have hbp' : StageSpace HighQueryProgram.branch nb a (max D (40*(H.card+1))) :=
      ⟨fun k z hk hz i => (hbp.bound k z hk hz i).trans (Nat.le_max_left _ _)⟩
    have hdp' : StageSpace (advanceCmd highPorts.counter) na b (max D (40*(H.card+1))) := by
      constructor
      intro k z hk hz i
      exact (hdp.bound k z (hk.trans (Nat.le_succ _)) hz i).trans
        (max_le (Nat.le_max_right _ _) (BD.trans (Nat.le_max_left _ _)))
    have hbodySpace := StageSpace.seq he ha hbp' hdp'
    by_cases hz : fuel=0
    · subst fuel
      have hlast : CounterPrograms.value words.flatten+1=2^words.flatten.length := by
        rw [flattened_length H words shape,hv]
        omega
      have hcarry := (overflow_at_last words hlast).1
      have hfalse : next.regs 21=false := by
        change (advanceResult highPorts.counter b words).regs (highPorts.counter.register 2)=false
        rw [advanceResult_flag,hcarry]
        rfl
      have hdone : Eval (loopCmd highPorts.counter HighQueryProgram.branch) 1 next next :=
        .while_false hfalse
      have hdoneSpace : StageSpace (loopCmd highPorts.counter HighQueryProgram.branch) 1 next
          (max D (40*(H.card+1))) := by
        exact while_done_space _ _ _ next hfalse
          (fun i => (hdb i).trans (BD.trans (Nat.le_max_left _ _)))
      refine ⟨nb+na+1+1,next,.while_true hf hbody hdone,by omega,hdi,?_,hdl,hdo,hdt,?_,
        hds,hfalse,hdb,?_⟩
      · have heq : rank+1=2^H.card := by omega
        rw [heq,rankSum_fullCount] at hda
        exact hda
      · exact overflow_counter H words shape (by omega) b
      · exact while_step_space hf hbody hdone hbodySpace hdoneSpace
    · have hbefore : CounterPrograms.value words.flatten+1<2^words.flatten.length := by
        rw [flattened_length H words shape,hv]
        omega
      obtain ⟨hcarry,hvalue⟩ := advance_before_last words hbefore
      have htrue : next.regs 21=true := by
        change (advanceResult highPorts.counter b words).regs (highPorts.counter.register 2)=true
        rw [advanceResult_flag,hcarry]
        rfl
      have hshape := (bumpWords_lengths words).trans shape
      have hcounter : next.stacks 789=Encoding.encodeList id (bumpWords words).2 :=
        advanceResult_counter highPorts.counter b words
      obtain ⟨nt,c,heval,hnt,hci,hca,hcl,hco,hct,hcc,hcs,hcf,hcb,hcp⟩ :=
        ih (rank+1) (bumpWords words).2 next hshape hdi hcounter hds hdt htrue
          (by omega) (by omega) hda hdl hdb
      refine ⟨nb+na+nt+1,c,.while_true hf hbody heval,?_,hci,hca,hcl,hco,hct,hcc,hcs,hcf,hcb,?_⟩
      · rw [Nat.succ_mul]
        omega
      · exact while_step_space hf hbody heval hbodySpace hcp

/-- The real initializer, all high ranks, final overflow, false guard and
compiler halt are paid in one run. An empty high set still executes one
branch. The endpoint word bound is B, independently of the visit count. -/
theorem high_loop_run
    (stable : CounterForPrograms.FrameStable highPorts.counter (fun _ => I))
    (width : 4*H.card+1≤B) (BD : B≤D)
    (branch : ∀ (rank : ℕ), rank<2^H.card → ∀ (words : List (List Bool))
      (a : HighQueryAdapter.Data), words.map List.length=List.replicate H.card 1 → I a →
      a.stacks 789=Encoding.encodeList id words → a.stacks 790=[] →
      a.stacks 791=[] → a.regs 21=true → CounterPrograms.value words.flatten=rank →
      BinaryArithmetic.toNat (a.stacks 788)=rankSum (rankValue H hashes marked clause) 0 rank →
      (a.stacks 788).length≤n+1 → (∀ i,(a.stacks i).length≤B) →
      ∃ steps b, Eval HighQueryProgram.branch steps a b ∧ steps≤C ∧ I b ∧
        BinaryArithmetic.toNat (b.stacks 788)=
          rankSum (rankValue H hashes marked clause) 0 (rank+1) ∧
        (b.stacks 788).length≤n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
        b.stacks 789=a.stacks 789 ∧ b.stacks 790=a.stacks 790 ∧
        (∀ i,(b.stacks i).length≤B) ∧
        StageSpace HighQueryProgram.branch steps a D)
    (a : HighQueryAdapter.Data) (hi : I a)
    (hc : a.stacks 789=Encoding.encodeList id (List.replicate H.card [false]))
    (hs : a.stacks 790=[]) (ht : a.stacks 791=[])
    (hacc : BinaryArithmetic.toNat (a.stacks 788)=0)
    (hlen : (a.stacks 788).length≤n+1) (hb : ∀ i,(a.stacks i).length≤B) :
    ∃ steps b, Eval HighQueryProgram.highLoop steps a b ∧
      steps+1≤2^H.card*(C+28*H.card+12)+3 ∧ I b ∧
      BinaryArithmetic.toNat (b.stacks 788)=fullCount hashes marked clause ∧
      (b.stacks 788).length≤n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
      b.stacks 789=Encoding.encodeList id (List.replicate H.card [false]) ∧
      b.stacks 790=[] ∧ b.regs 21=false ∧ (∀ i,(b.stacks i).length≤B) ∧
      Trace (compiled HighQueryProgram.highLoop 789 788) (steps+1)
        (a.withPC (some (compiled HighQueryProgram.highLoop 789 788).entry)) (b.withPC none) ∧
      StageSpace HighQueryProgram.highLoop (steps+1) a (max D (40*(H.card+1))) := by
  let started := startResult highPorts.counter a
  have hstart : Eval (startCmd highPorts.counter) 1 a started := .base (.atom _ _)
  have hi' : I started := stable 0 a started (fun _ _ _ => rfl) hi
  have shape : (List.replicate H.card [false]).map List.length=List.replicate H.card 1 := by simp
  have hz : CounterPrograms.value (List.replicate H.card [false]).flatten=0 :=
    zero_tuple_value H.card 1
  have hac : BinaryArithmetic.toNat (started.stacks 788)=
      rankSum (rankValue H hashes marked clause) 0 0 := by
    change BinaryArithmetic.toNat (a.stacks 788)=_
    simpa only [rankSum,List.range'_zero,List.map_nil,List.sum_nil] using hacc
  obtain ⟨nt,b,he,hnt,hbi,hba,hbl,hbo,hbt,hbc,hbs,hbf,hbb,hbp⟩ :=
    loop_run H hashes marked clause I B C D stable width BD branch (2^H.card)
      0 (List.replicate H.card [false]) started shape hi' hc hs ht
      (startResult_flag highPorts.counter a) hz (by omega) hac hlen hb
  have hwhole : Eval HighQueryProgram.highLoop (1+nt) a b := hstart.seq he
  have hstartSpace : StageSpace (startCmd highPorts.counter) 1 a (max D (40*(H.card+1))) := by
    constructor
    intro k z hk hz i
    have hk' : k=0 ∨ k=1 := by omega
    rcases hk' with rfl|rfl
    · cases hz
      exact (hb i).trans (BD.trans (Nat.le_max_left _ _))
    · rw [trace_same_length_unique hz (compiled_trace hstart 778 777)]
      exact (hb i).trans (BD.trans (Nat.le_max_left _ _))
  have hp := StageSpace.seq hstart he hstartSpace hbp
  refine ⟨1+nt,b,hwhole,by omega,hbi,hba,hbl,hbo,hbt,hbc,hbs,hbf,hbb,
    compiled_halt_trace hwhole 789 788,?_⟩
  exact ⟨StructuredSpace.compiled_halt_stack_bound hwhole 778 777 hp.bound⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal
