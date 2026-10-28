import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit

/-! Each marked count regenerates its own zero high-assignment odometer from
its current physical mask. No common high set or retained previous seed is
assumed. The original two-stack branch initializer is executed concretely. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed

open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def changed : List (Fin 896) := [330,791,792]
def reset : Code := .seq (.call (clearProgram 791 0 1))
  (BankRoutines.clearCmd 791 0 1 changed)
def resetState (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks changed a.stacks⟩
def resetCost (a : Data) := 2*(a.stacks 791).length+3+
  (2*(changed.map (fun i => ((clearStacks 791 a.stacks) i).length)).sum+12)

theorem reset_eval (a : Data) : Eval reset (resetCost a) a (resetState a) := by
  have h1 := BankRoutines.clear_call_eval (791 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_eval (791 : Fin 896) (0 : Fin 40) 1 changed (by decide)
    (readRegs a.regs 0 1 none) (clearStacks 791 a.stacks) (by simp)
  have hs : BankRoutines.clearBankStacks changed (clearStacks 791 a.stacks)=
      BankRoutines.clearBankStacks changed a.stacks := by
    funext i
    by_cases hi : i∈changed
    · simp [BankRoutines.clearBankStacks,hi]
    · have hn : i≠791 := by intro h; subst i; exact hi (by decide)
      simp [BankRoutines.clearBankStacks,clearStacks,hi,hn]
  simpa only [reset,resetCost,resetState,show changed.length=3 from rfl,
    hs,readRegs_reset] using h1.seq h2

theorem reset_frame (a : Data) (i : Fin 896) (hi : i∉changed) :
    (resetState a).stacks i=a.stacks i := BankRoutines.clearBankStacks_frame i changed a.stacks hi

theorem reset_blank (a : Data) (i : Fin 896) (hi : i∈changed) :
    (resetState a).stacks i=[] := BankRoutines.clearBankStacks_mem i changed a.stacks hi

def copy : Code := .call (copyProgram 338 792 791 0 1)
def copied (a : Data) : Data :=
  ⟨readRegs (resetState a).regs 0 1 none,copyStacks 338 792 (resetState a).stacks⟩
def regMap : Fin 2 → Fin 40 := Fin.castAdd 38
def stackMap : Fin 2 → Fin 896 := ![792,330]
def branch : Code := .call (ProgramLinking.liftProgram Branches.program regMap stackMap)
noncomputable def result (a : Data) (rf : Fin 2 → Bool) : Data :=
  embedState regMap stackMap (copied a) (Branches.state rf []
    (Encoding.encodeList id (List.replicate (Branches.trueCount (a.stacks 338)) [false])))
def command : Code := .seq reset (.seq copy branch)
def program := compiled command 338 330
def cost (a : Data) := resetCost a+10*(a.stacks 338).length+
  8*Branches.trueCount (a.stacks 338)+10

@[simp] theorem result_counter (a : Data) (rf : Fin 2 → Bool) :
    (result a rf).stacks 330=Encoding.encodeList id
      (List.replicate (Branches.trueCount (a.stacks 338)) [false]) :=
  embedState_stack regMap stackMap (copied a) _ (by decide) 1

@[simp] theorem result_maskcopy (a : Data) (rf : Fin 2 → Bool) :
    (result a rf).stacks 792=[] := embedState_stack regMap stackMap (copied a) _ (by decide) 0

theorem result_frame (a : Data) (rf : Fin 2 → Bool) (i : Fin 896) (hi : i∉changed) :
    (result a rf).stacks i=a.stacks i := by
  have hn : ¬∃ j,stackMap j=i := by
    rintro ⟨j,rfl⟩
    fin_cases j <;> simp [stackMap,changed] at hi
  rw [show (result a rf).stacks i=(copied a).stacks i from
    embedState_stack_frame regMap stackMap (copied a) _ i hn]
  have h792 : i≠792 := by intro h; subst i; exact hi (by decide)
  simp [copied,copyStacks,h792,reset_frame a i hi]

@[simp] theorem result_scratch (a : Data) (rf : Fin 2 → Bool) : (result a rf).stacks 791=[] := by
  rw [show (result a rf).stacks 791=(copied a).stacks 791 from
    embedState_stack_frame regMap stackMap (copied a) _ 791 (by decide)]
  simp [copied,copyStacks,reset_blank a 791 (by decide)]

theorem copy_eval (a : Data) : Eval copy (7*(a.stacks 338).length+5) (resetState a) (copied a) := by
  unfold copy copied
  apply Eval.call
  simpa only [reset_frame a 338 (by decide)] using
    ListRegisterProgram.copy_run (338 : Fin 896) 792 791 (0 : Fin 40) 1
      (by decide) (by decide) (by decide) (by decide)
      (resetState a).regs (resetState a).stacks (reset_blank a 791 (by decide))

private theorem project_copied (a : Data) : projectState regMap stackMap (copied a)=
    Branches.state ((copied a).regs ∘ regMap) (a.stacks 338) [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [stackMap, copied, copyStacks,
      reset_blank a 792 (by decide),reset_blank a 330 (by decide),reset_frame a 338 (by decide)]

theorem branch_eval (a : Data) : ∃ rf, Eval branch
    (3*(a.stacks 338).length+8*Branches.trueCount (a.stacks 338)+5) (copied a) (result a rf) := by
  obtain ⟨rf,he⟩ := Branches.command_eval ((copied a).regs ∘ regMap) (a.stacks 338)
  have ht := compiled_halt_trace he 0 1
  rw [←project_copied a] at ht
  have h := eval_call_from_state Branches.program regMap stackMap (copied a)
    (Fin.castAdd_injective _ _) (by decide) ht
  refine ⟨rf,?_⟩
  exact h

theorem command_eval (a : Data) : ∃ rf, Eval command (cost a) a (result a rf) := by
  obtain ⟨rf,h⟩ := branch_eval a
  refine ⟨rf,?_⟩
  convert (reset_eval a).seq ((copy_eval a).seq h) using 1
  · rfl
  · dsimp [cost]
    omega

private theorem reset_bound (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ i, ((resetState a).stacks i).length≤bound := by
  intro i
  by_cases hi : i∈changed
  · rw [reset_blank a i hi]; exact Nat.zero_le _
  · rw [reset_frame a i hi]; exact hb i

private theorem copied_bound (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ i, ((copied a).stacks i).length≤bound := by
  intro i
  by_cases hi : i=792
  · subst i
    simpa [copied,copyStacks,reset_blank a 792 (by decide),reset_frame a 338 (by decide)] using hb 338
  · simpa [copied,copyStacks,hi] using reset_bound a bound hb i

private theorem reset_space (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ q z, q≤resetCost a → Trace (compiled reset 338 330) q
      (a.withPC (some (compiled reset 338 330).entry)) z → ∀ i, (z.stacks i).length≤bound := by
  let middle : Data := ⟨readRegs a.regs 0 1 none,clearStacks 791 a.stacks⟩
  have first := BankRoutines.clear_call_eval (791 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have rest := BankRoutines.clear_eval (791 : Fin 896) (0 : Fin 40) 1 changed
    (by decide) middle.regs middle.stacks (by simp [middle])
  have hfirst := HighQuerySpace.clear_bound (791 : Fin 896) (0 : Fin 40) 1 a bound hb 338 330
  have hrest := HighQuerySpace.clear_bank_bound (791 : Fin 896) (0 : Fin 40) 1 changed
    (by decide) middle (by simp [middle]) bound
    (HighQuerySpace.clear_state_bound 791 0 1 a bound hb) 338 330
  exact StructuredSpace.sequence_stack_bound first rest 338 330 hfirst hrest
    _ _ _ (compiled_site reset 338 330)

private theorem copy_space (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ q z, q≤7*(a.stacks 338).length+5 → Trace (compiled copy 338 330) q
      ((resetState a).withPC (some (compiled copy 338 330).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
  have he := copy_eval a
  cases he with
  | call p tr =>
    apply StructuredSpace.call_stack_bound _ _ _ _ (compiled_site copy 338 330) tr
    intro q z _ hq
    exact CopySpace.copyProgram_no_growth 338 792 791 0 1 (by decide) (by decide) (by decide)
      rfl (reset_blank a 792 (by decide)) (reset_blank a 791 (by decide)) (reset_bound a bound hb) hq

private theorem branch_space (a : Data) (localCap bound : ℕ)
    (hm : (a.stacks 338).length≤localCap) (hbudget : 12*localCap+5≤bound)
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ rf, Eval branch (3*(a.stacks 338).length+8*Branches.trueCount (a.stacks 338)+5)
      (copied a) (result a rf) ∧
      ∀ q z, q≤3*(a.stacks 338).length+8*Branches.trueCount (a.stacks 338)+5 →
        Trace (compiled branch 338 330) q
          ((copied a).withPC (some (compiled branch 338 330).entry)) z →
          ∀ i, (z.stacks i).length≤bound := by
  obtain ⟨rf,he⟩ := Branches.command_eval ((copied a).regs ∘ regMap) (a.stacks 338)
  have ht : Trace Branches.program (3*(a.stacks 338).length+8*Branches.trueCount (a.stacks 338)+5)
      ((Branches.state ((copied a).regs ∘ regMap) (a.stacks 338) []).withPC
        (some Branches.program.entry))
      ((Branches.state rf [] (Encoding.encodeList id
        (List.replicate (Branches.trueCount (a.stacks 338)) [false]))).withPC none) := by
    exact compiled_halt_trace he 0 1
  have hlocal : ∀ q z, q≤3*(a.stacks 338).length+8*Branches.trueCount (a.stacks 338)+5 →
      Trace Branches.program q
        ((Branches.state ((copied a).regs ∘ regMap) (a.stacks 338) []).withPC
          (some Branches.program.entry)) z → ∀ i, (z.stacks i).length≤bound := by
    have hi : dataBits ((Branches.state ((copied a).regs ∘ regMap) (a.stacks 338) []).withPC
        (some Branches.program.entry))≤localCap := by
      simpa [dataBits,stackBits,Branches.state,Fin.sum_univ_two,StructuredProgram.State.withPC] using hm
    have hc : Branches.trueCount (a.stacks 338)≤(a.stacks 338).length := List.length_filter_le _ _
    intro q z hq hz i
    have h := StructuredSpace.local_stack_bound Branches.program (steps:=11*localCap+5) hi
      q z (by omega) hz i
    omega
  have hex := eval_call_from_state Branches.program regMap stackMap (copied a)
    (Fin.castAdd_injective _ _) (by decide) (by simpa only [project_copied a] using ht)
  refine ⟨rf,hex,?_⟩
  exact HighQuerySpace.lifted_call_bound Branches.program regMap stackMap
    (Fin.castAdd_injective _ _) (by decide) (copied a) _ _ (project_copied a) _ bound ht
    hlocal (copied_bound a bound hb) 338 330

/-- Actual current-mask seed generation, with one fixed all-prefix envelope. -/
theorem trace_space (a : Data) (localCap bound : ℕ)
    (hm : (a.stacks 338).length≤localCap) (hbudget : 12*localCap+5≤bound)
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ rf, Trace program (cost a+1) (a.withPC (some program.entry)) ((result a rf).withPC none) ∧
      cost a+1≤8*bound+18*(a.stacks 338).length+26 ∧
      ∀ q z, q≤cost a+1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length≤bound := by
  obtain ⟨rf,he,hbranch⟩ := branch_space a localCap bound hm hbudget hb
  have htail := StructuredSpace.sequence_stack_bound (copy_eval a) he 338 330
    (copy_space a bound hb) hbranch _ _ _ (compiled_site (.seq copy branch) 338 330)
  have hwhole := StructuredSpace.sequence_stack_bound (reset_eval a) ((copy_eval a).seq he)
    338 330 (reset_space a bound hb) htail _ _ _ (compiled_site command 338 330)
  have heval : Eval command (cost a) a (result a rf) := by
    convert (reset_eval a).seq ((copy_eval a).seq he) using 1
    · rfl
    · dsimp [cost]
      omega
  have hsum : (changed.map (fun i => ((clearStacks 791 a.stacks) i).length)).sum≤3*bound := by
    apply (List.sum_le_length_nsmul _ bound (by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      by_cases heq : i=791
      · subst i; simp [clearStacks]
      · simpa [clearStacks,heq] using hb i)).trans_eq
    simp [changed]
  have htime : cost a+1≤8*bound+18*(a.stacks 338).length+26 := by
    have ht := hb 791
    have hc : Branches.trueCount (a.stacks 338)≤(a.stacks 338).length := List.length_filter_le _ _
    dsimp [cost,resetCost]
    omega
  refine ⟨rf,compiled_halt_trace heval 338 330,htime,?_⟩
  apply StructuredSpace.compiled_halt_stack_bound heval 338 330
  intro q z hq hz
  apply hwhole q z _ hz
  dsimp [cost] at hq
  omega

/-- Actual per-mark entry: regenerate from this mask, then initializeCmd the
fixed durable high counter and empty binary count buffers. -/
def initializeCmd : Code := .seq (.call program) (.call HighCountInit.program)
def initializeProgram := compiled initializeCmd 338 789
noncomputable def initialized (a : Data) (rf : Fin 2 → Bool) : Data := HighCountInit.result (result a rf)

@[simp] theorem initialized_counter (a : Data) (rf : Fin 2 → Bool) :
    (initialized a rf).stacks 789=Encoding.encodeList id
      (List.replicate (Branches.trueCount (a.stacks 338)) [false]) := by
  rw [initialized,HighCountInit.counter,result_counter]

@[simp] theorem initialized_blank (a : Data) (rf : Fin 2 → Bool) (i : Fin 896)
    (hi : i∈([788,790,323,791,792] : List (Fin 896))) :
    (initialized a rf).stacks i=[] := HighCountInit.blank (result a rf) i hi

theorem initialized_frame (a : Data) (rf : Fin 2 → Bool) (i : Fin 896)
    (hi : i∉([330,788,789,790,323,791,792] : List (Fin 896))) :
    (initialized a rf).stacks i=a.stacks i := by
  have hinit : i∉HighCountInit.changed := by simp only [HighCountInit.changed] ; simpa using
    (fun (h : i∈([788,789,790,323,791,792] : List (Fin 896))) => hi (List.mem_cons_of_mem _ h))
  have hseed : i∉changed := by
    simp only [changed,List.mem_cons,List.not_mem_nil,or_false] at *
    tauto
  exact (HighCountInit.frame (result a rf) i hinit).trans (result_frame a rf i hseed)

@[simp] theorem initialized_guard (a : Data) (rf : Fin 2 → Bool) :
    (initialized a rf).regs 21=true := HighCountInit.guard (result a rf)

/-- Seed WORD length is linear in the mask, including the empty-high singleton
terminator. Counter numerical value is zero regardless of ambient dimension. -/
theorem initialized_counter_length (a : Data) (rf : Fin 2 → Bool) :
    ((initialized a rf).stacks 789).length=4*Branches.trueCount (a.stacks 338)+1 := by
  rw [initialized_counter,ExecCNFTupleOdometer.encoded_length]
  simp
  omega

theorem initialized_ready {I : Data → Prop} (a : Data) (rf : Fin 2 → Bool)
    (hi : I (initialized a rf)) : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram.Ready highPorts I (initialized a rf) :=
  HighCountInit.ready (result a rf) hi

/-- No supplied zero counter appears in this concrete entry theorem. Both
resource bounds belong to the very same actual complete source run. -/
theorem initialize_trace_space (a : Data) (localCap bound : ℕ)
    (hm : (a.stacks 338).length≤localCap) (hbudget : 12*localCap+5≤bound)
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ steps rf, Trace initializeProgram steps (a.withPC (some initializeProgram.entry))
      ((initialized a rf).withPC none) ∧
      steps ≤ 29 * bound + 18 * (a.stacks 338).length + 58 ∧
      ∀ (q : ℕ) z, q ≤ steps → Trace initializeProgram q
        (a.withPC (some initializeProgram.entry)) z → ∀ i, (z.stacks i).length≤bound := by
  obtain ⟨rf,hs,hstime,hsp⟩ := trace_space a localCap bound hm hbudget hb
  have hb' := hsp _ _ le_rfl hs
  obtain ⟨hi,hitime,hip⟩ := HighCountInit.trace_space (result a rf) bound hb'
  have hes := Eval.call program hs
  have hei := Eval.call HighCountInit.program hi
  have hfirst := StructuredSpace.call_stack_bound _ _ _ _
    (compiled_site (.call program) 338 789) hs hsp
  have hsecond := StructuredSpace.call_stack_bound _ _ _ _
    (compiled_site (.call HighCountInit.program) 338 789) hi hip
  have hwhole := StructuredSpace.sequence_stack_bound hes hei 338 789 hfirst hsecond
    _ _ _ (compiled_site initializeCmd 338 789)
  have heval := hes.seq hei
  exact ⟨_,rf,compiled_halt_trace heval 338 789,by omega,
    StructuredSpace.compiled_halt_stack_bound heval 338 789 hwhole⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed
