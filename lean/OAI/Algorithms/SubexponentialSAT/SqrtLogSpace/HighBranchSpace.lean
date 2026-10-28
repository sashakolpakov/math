import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit

/-! Actual high-condition staging uses a fixed local ten-stack footprint.
The independent physical cap is never identified with a sum of caller words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace

open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

abbrev Data := State 40 896

/-- The actual one-bit tuple odometer is decoded in the descending physical
high-coordinate order, then returned to ascending ambient coordinates. -/
theorem rank_high_vector_semantics {n : ℕ} (H : Finset (Fin n))
    (words : List (List Bool)) (hshape : words.map List.length=List.replicate H.card 1)
    (rank : Fin (2^H.card)) (hrank : CounterPrograms.value words.flatten=rank.val) :
    (Restriction.zeroMerge (SqrtLogSpace.HighIncidenceProgram.descendingHighMask H)
      words.flatten).reverse =
      List.ofFn (HighIncidence.glue H (Rank.highEquiv (Order.highOrder H) rank)
        (fun _ => false)) := by
  have ht := Rank.tuple_of_rank words hshape rank hrank
  have hflat : words.flatten=List.ofFn (Rank.assignment H.card rank) := by
    rw [ht]
    generalize List.ofFn (Rank.assignment H.card rank)=xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih]
  have horder : List.ofFn (fun i =>
      Rank.highEquiv (Order.highOrder H) rank (Order.highOrder H i)) =
      List.ofFn (Rank.assignment H.card rank) := by
    congr 1
    funext i
    simp [Rank.highEquiv,Rank.reindex,Rank.assignment]
  rw [hflat,←horder]
  exact high_vector_semantics H (Rank.highEquiv (Order.highOrder H) rank)

private theorem high_scratch (a : Data) (regs : Fin 4 → Bool) (high : List Bool)
    (i : Fin 896) (hi : i∈([680,681,682,683,684,685] : List (Fin 896))) :
    (highResult a regs high).stacks i=[] := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
  · exact embedState_stack highRegs highStacks a _ (by decide) 4
  · exact embedState_stack highRegs highStacks a _ (by decide) 5
  · exact embedState_stack highRegs highStacks a _ (by decide) 6
  · exact embedState_stack highRegs highStacks a _ (by decide) 7
  · exact embedState_stack highRegs highStacks a _ (by decide) 8
  · exact embedState_stack highRegs highStacks a _ (by decide) 9

private theorem reset_bound (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ i, ((resetHighState a).stacks i).length≤bound := by
  intro i
  by_cases hi : i∈highChanged
  · simp [resetHighState,BankRoutines.clearBankStacks,hi]
  · rw [resetHigh_frame a i hi]; exact hb i

/-- Exact outputs are ambient-length words; all consumed parser buffers are
empty. This is the repeated boundary invariant, independently of transient cost. -/
theorem result_bound (a : Data) (regs : Fin 4 → Bool) (high : List Bool) (bound : ℕ)
    (hh : high.length=Restriction.highCount (a.stacks 338))
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ i, ((highResult a regs high).stacks i).length≤bound := by
  intro i
  by_cases hm : i=702
  · subst i; rw [highResult_mask,List.length_reverse]; exact hb 338
  · by_cases hh' : i=703
    · subst i
      rw [highResult_bits,List.length_reverse,(Restriction.zeroMerge_spec _ _ hh).1]
      exact hb 338
    · by_cases hs : i∈([680,681,682,683,684,685] : List (Fin 896))
      · rw [high_scratch a regs high i hs]; exact Nat.zero_le _
      · rw [highResult_frame a regs high i (by simpa [highChanged,hm,hh'] using hs)]
        exact hb i

theorem prepared_branch_bound (a : Data) (regs : Fin 4 → Bool) (high : List Bool) (bound : ℕ)
    (hh : high.length=Restriction.highCount (a.stacks 338))
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ i, ((highResult (resetHighState (copiedHighCounter a)) regs high).stacks i).length≤bound := by
  apply result_bound _ _ _ bound _ (reset_bound _ _ (copiedHighCounter_bound a bound hb))
  simpa only [resetHigh_frame _ 338 (by decide),copiedHighCounter_frame a 338 (by decide) (by decide)] using hh

private theorem reset_space (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound)
    (input output : Fin 896) :
    ∀ (q : ℕ) z, q ≤ resetHighCost a → Trace (compiled resetHigh input output) q
      (a.withPC (some (compiled resetHigh input output).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
  let middle : Data := ⟨readRegs a.regs 0 1 none,clearStacks 702 a.stacks⟩
  have first := BankRoutines.clear_call_eval (702 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have rest := BankRoutines.clear_eval (702 : Fin 896) (0 : Fin 40) 1 highChanged
    (by decide) middle.regs middle.stacks (by simp [middle])
  have hfirst := HighQuerySpace.clear_bound (702 : Fin 896) (0 : Fin 40) 1 a bound hb input output
  have hrest := HighQuerySpace.clear_bank_bound (702 : Fin 896) (0 : Fin 40) 1 highChanged
    (by decide) middle (by simp [middle]) bound
    (HighQuerySpace.clear_state_bound 702 0 1 a bound hb) input output
  exact StructuredSpace.sequence_stack_bound first rest input output hfirst hrest
    _ _ _ (compiled_site resetHigh input output)

/-- Only the physical encoded counter and ambient mask enter the local cap. -/
theorem high_command_space (a : Data) (words : List (List Bool)) (h localCap bound : ℕ)
    (input output : Fin 896)
    (hc : a.stacks 330=ProgramEncoding.encodeRecords words)
    (he : ∀ i∈highChanged, a.stacks i=[])
    (hshape : words.map List.length=List.replicate h 1)
    (hh : h=Restriction.highCount (a.stacks 338))
    (hcounter : (a.stacks 330).length≤localCap) (hmask : (a.stacks 338).length≤localCap)
    (hbudget : 67*localCap+37≤bound) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ steps regs, Eval highCommand steps a (highResult a regs words.flatten) ∧
      steps ≤ 65 * (a.stacks 338).length + 37 ∧
      ∀ (q : ℕ) z, q ≤ steps → Trace (compiled highCommand input output) q
        (a.withPC (some (compiled highCommand input output).entry)) z →
        ∀ i, (z.stacks i).length≤bound := by
  have hw : words.length=h := by
    have ht := congrArg List.length hshape
    simpa only [List.length_map,List.length_replicate] using ht
  have hf : words.flatten.length=h := by rw [List.length_flatten,hshape]; simp
  have henc : (ProgramEncoding.encodeRecords words).length=4*h+1 := by
    rw [show ProgramEncoding.encodeRecords words=Encoding.encodeList id words from rfl,
      ExecCNFTupleOdometer.encoded_length,hf,hw]
    omega
  have hdim : h≤(a.stacks 338).length := by rw [hh]; exact List.length_filter_le _ _
  have hp : projectState highRegs highStacks a=
      LeafHighContextProgram.Local.state (a.regs ∘ highRegs)
        (ProgramEncoding.encodeRecords words) (a.stacks 338) [] [] [] [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [highStacks, LeafHighContextProgram.Local.tapes, hc,
        he 702 (by simp [highChanged]),he 703 (by simp [highChanged]),
        he 680 (by simp [highChanged]),he 681 (by simp [highChanged]),
        he 682 (by simp [highChanged]),he 683 (by simp [highChanged]),
        he 684 (by simp [highChanged]),he 685 (by simp [highChanged])]
  obtain ⟨rf,steps,hn,ht⟩ := LeafHighContextProgram.Local.runsIn
    (a.regs ∘ highRegs) words (a.stacks 338) (hf.trans hh)
  have htime : steps ≤ 65 * (a.stacks 338).length + 37 := by
    unfold LeafHighContextProgram.Local.cost at hn
    rw [henc,hf,hw] at hn
    omega
  have hinit : dataBits ((LeafHighContextProgram.Local.state (a.regs ∘ highRegs)
      (ProgramEncoding.encodeRecords words) (a.stacks 338) [] [] [] [] [] [] [] []).withPC
        (some LeafHighContextProgram.Local.program.entry))≤2*localCap := by
    have hc' : (ProgramEncoding.encodeRecords words).length≤localCap := by rwa [←hc]
    simp only [dataBits, stackBits,
      LeafHighContextProgram.Local.state,LeafHighContextProgram.Local.tapes]
    norm_num [Fin.sum_univ_succ]
    omega
  have hlocal : ∀ (q : ℕ) z, q ≤ steps → Trace LeafHighContextProgram.Local.program q
      ((LeafHighContextProgram.Local.state (a.regs ∘ highRegs)
        (ProgramEncoding.encodeRecords words) (a.stacks 338) [] [] [] [] [] [] [] []).withPC
          (some LeafHighContextProgram.Local.program.entry)) z →
        ∀ i, (z.stacks i).length≤bound := by
    intro q z hq hz i
    have h := StructuredSpace.local_stack_bound LeafHighContextProgram.Local.program
      (steps:=65*localCap+37) hinit q z (by omega) hz i
    omega
  rw [←hp] at ht hlocal
  have heval := eval_call_from_state LeafHighContextProgram.Local.program highRegs highStacks a
    (Fin.castAdd_injective _ _) (by decide) ht
  have hglobal := StructuredSpace.liftProgram_stack_bound LeafHighContextProgram.Local.program
    highRegs highStacks (a.withPC none) (Fin.castAdd_injective _ _) (by decide) ht hlocal hb
  have hstart : ProgramLinking.embedCfg highRegs highStacks id none (a.withPC none)
      ((projectState highRegs highStacks a).withPC (some LeafHighContextProgram.Local.program.entry))=
      a.withPC (some (ProgramLinking.liftProgram LeafHighContextProgram.Local.program highRegs highStacks).entry) := by
    change (embedState highRegs highStacks a (projectState highRegs highStacks a)).withPC _ = _
    rw [embedState_project highRegs highStacks a (Fin.castAdd_injective _ _) (by decide)]
    rfl
  rw [hstart] at hglobal
  simp only [Nat.max_self] at hglobal
  refine ⟨steps,rf,?_,htime,?_⟩
  · simpa only [highCommand,highResult,hc] using heval
  · cases heval with
    | call p tr =>
      exact StructuredSpace.call_stack_bound _ _ _ _
        (compiled_site highCommand input output) tr hglobal

theorem prepare_high_space (a : Data) (words : List (List Bool)) (h localCap bound : ℕ)
    (input output : Fin 896)
    (hc : a.stacks 330=ProgramEncoding.encodeRecords words)
    (hshape : words.map List.length=List.replicate h 1)
    (hh : h=Restriction.highCount (a.stacks 338))
    (hcounter : (a.stacks 330).length≤localCap) (hmask : (a.stacks 338).length≤localCap)
    (hbudget : 67*localCap+37≤bound) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ steps regs, Trace (compiled prepareHigh input output) steps
      (a.withPC (some (compiled prepareHigh input output).entry))
      ((highResult (resetHighState a) regs words.flatten).withPC none) ∧
      steps ≤ 18 * bound + 65 * (a.stacks 338).length + 68 ∧
      ∀ (q : ℕ) z, q ≤ steps → Trace (compiled prepareHigh input output) q
        (a.withPC (some (compiled prepareHigh input output).entry)) z →
        ∀ i, (z.stacks i).length≤bound := by
  have hm := resetHigh_frame a 338 (by decide)
  have hc' := resetHigh_frame a 330 (by decide)
  obtain ⟨steps,regs,he,ht,hspace⟩ := high_command_space
    (resetHighState a) words h localCap bound input output
    (hc'.trans hc) (fun i hi => BankRoutines.clearBankStacks_mem i highChanged a.stacks hi)
    hshape (by simpa only [hm] using hh) (by simpa only [hc'] using hcounter)
    (by simpa only [hm] using hmask) hbudget (reset_bound a bound hb)
  have hex := (resetHigh_eval a).seq he
  have hwhole := StructuredSpace.sequence_stack_bound (resetHigh_eval a) he input output
    (reset_space a bound hb input output) hspace _ _ _
    (compiled_site prepareHigh input output)
  have hsum : (highChanged.map (fun i => ((clearStacks 702 a.stacks) i).length)).sum≤8*bound := by
    apply (List.sum_le_length_nsmul _ bound (by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      by_cases heq : i=702
      · subst i; simp [clearStacks]
      · simpa [clearStacks,heq] using hb i)).trans_eq
    simp [highChanged]
  have hreset : resetHighCost a≤18*bound+30 := by
    dsimp [resetHighCost]
    have := hb 702
    omega
  refine ⟨resetHighCost a+steps+1,regs,compiled_halt_trace hex input output,?_,
    StructuredSpace.compiled_halt_stack_bound hex input output hwhole⟩
  rw [hm] at ht
  omega

/-- Staging the durable counter into the old lower port is a restoring copy
with empty destination and temporary, so its all-stack envelope is unchanged. -/
theorem copy_high_space (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ (q : ℕ) z, q ≤ copyHighCost a → Trace (compiled copyHighCounter 789 703) q
      (a.withPC (some (compiled copyHighCounter 789 703).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
  let b : Data := ⟨readRegs a.regs 0 1 none,clearStacks 330 a.stacks⟩
  let c : Data := ⟨readRegs b.regs 0 1 none,clearStacks 792 b.stacks⟩
  have h1 : Eval (.call (clearProgram (330 : Fin 896) (0 : Fin 40) 1))
      (2*(a.stacks 330).length+3) a b :=
    BankRoutines.clear_call_eval 330 0 1 a.regs a.stacks
  have h2 : Eval (.call (clearProgram (792 : Fin 896) (0 : Fin 40) 1))
      (2*(b.stacks 792).length+3) b c :=
    BankRoutines.clear_call_eval 792 0 1 b.regs b.stacks
  have h3 : Eval (.call (copyProgram (789 : Fin 896) 330 792 (0 : Fin 40) 1))
      (7*(c.stacks 789).length+5) c
      ⟨readRegs c.regs 0 1 none,copyStacks 789 330 c.stacks⟩ :=
    .call _ (ListRegisterProgram.copy_run 789 330 792 0 1
      (by decide) (by decide) (by decide) (by decide) c.regs c.stacks (by simp [c]))
  have hb' : ∀ i, (b.stacks i).length≤bound := HighQuerySpace.clear_state_bound 330 0 1 a bound hb
  have hc' : ∀ i, (c.stacks i).length≤bound := HighQuerySpace.clear_state_bound 792 0 1 b bound hb'
  have hfirst := HighQuerySpace.clear_bound (330 : Fin 896) (0 : Fin 40) 1 a bound hb 789 703
  have hsecond := HighQuerySpace.clear_bound (792 : Fin 896) (0 : Fin 40) 1 b bound hb' 789 703
  have hthird : ∀ (q : ℕ) z, q ≤ 7 * (c.stacks 789).length + 5 →
      Trace (compiled (.call (copyProgram (789 : Fin 896) 330 792 (0 : Fin 40) 1)) 789 703) q
        (c.withPC (some (compiled (.call (copyProgram (789 : Fin 896) 330 792 (0 : Fin 40) 1)) 789 703).entry)) z →
        ∀ i, (z.stacks i).length≤bound := by
    cases h3 with
    | call p tr =>
      apply StructuredSpace.call_stack_bound _ _ _ _
        (compiled_site (.call (copyProgram (789 : Fin 896) 330 792 (0 : Fin 40) 1)) 789 703) tr
      intro q z _ hq
      exact CopySpace.copyProgram_no_growth 789 330 792 0 1
        (by decide) (by decide) (by decide) rfl (by simp [c, b, clearStacks])
        (by simp [c]) hc' hq
  have htail := StructuredSpace.sequence_stack_bound h2 h3 789 703 hsecond hthird
    _ _ _ (compiled_site (.seq (.call (clearProgram 792 0 1))
      (.call (copyProgram 789 330 792 0 1))) 789 703)
  have hwhole := StructuredSpace.sequence_stack_bound h1 (h2.seq h3) 789 703 hfirst htail
    _ _ _ (compiled_site copyHighCounter 789 703)
  have hc789 : c.stacks 789=a.stacks 789 := by simp [c,b,clearStacks]
  have hb792 : b.stacks 792=a.stacks 792 := by simp [b,clearStacks]
  intro q z hq hz
  apply hwhole q z _ hz
  rw [hc789,hb792]
  dsimp [copyHighCost] at hq
  omega

/-- The actual repeated branch adapter keeps one fixed envelope on every
prefix. The local input cap is independent of all retained query/DFS words. -/
theorem prepare_branch_space (a : Data) (words : List (List Bool)) (h localCap bound : ℕ)
    (hc : a.stacks 789=ProgramEncoding.encodeRecords words)
    (hshape : words.map List.length=List.replicate h 1)
    (hh : h=Restriction.highCount (a.stacks 338))
    (hcounter : (a.stacks 789).length≤localCap) (hmask : (a.stacks 338).length≤localCap)
    (hbudget : 67*localCap+37≤bound) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ steps regs, Trace prepareBranchProgram steps (a.withPC (some prepareBranchProgram.entry))
      ((highResult (resetHighState (copiedHighCounter a)) regs words.flatten).withPC none) ∧
      steps ≤ 29 * bound + 65 * (a.stacks 338).length + 80 ∧
      ∀ (q : ℕ) z, q ≤ steps → Trace prepareBranchProgram q
        (a.withPC (some prepareBranchProgram.entry)) z → ∀ i, (z.stacks i).length≤bound := by
  have hm := copiedHighCounter_frame a 338 (by decide) (by decide)
  obtain ⟨steps,regs,ht,htime,hspace⟩ := prepare_high_space
    (copiedHighCounter a) words h localCap bound 330 703
    (by simpa only [copiedHighCounter_word] using hc) hshape
    (by simpa only [hm] using hh) (by simpa only [copiedHighCounter_word] using hcounter)
    (by simpa only [hm] using hmask) hbudget (copiedHighCounter_bound a bound hb)
  have he := Eval.call prepareHighProgram ht
  have hcall := StructuredSpace.call_stack_bound _ _ _ _
    (compiled_site (.call prepareHighProgram) 789 703) ht hspace
  have hex := (copyHighCounter_eval a).seq he
  have hwhole := StructuredSpace.sequence_stack_bound (copyHighCounter_eval a) he 789 703
    (copy_high_space a bound hb) hcall _ _ _ (compiled_site prepareBranch 789 703)
  have hcopy : copyHighCost a≤11*bound+11 := by
    dsimp [copyHighCost]
    have := hb 330
    have := hb 792
    have := hb 789
    omega
  refine ⟨copyHighCost a+steps+1,regs,compiled_halt_trace hex 789 703,?_,
    StructuredSpace.compiled_halt_stack_bound hex 789 703 hwhole⟩
  rw [hm] at htime
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace
