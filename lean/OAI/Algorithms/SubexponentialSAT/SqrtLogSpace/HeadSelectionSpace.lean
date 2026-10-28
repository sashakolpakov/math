import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CopySpace

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSelectionSpace
open BitProgram StructuredCalls StackRoutines
open HighQueryAdapter
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

/-- Reset never grows a retained caller stack, even when an old output word
must first be physically cleared. -/
theorem reset_bound (a : State 40 896) (B : ℕ)
    (ha : ∀ i,(a.stacks i).length≤B) :
    ∀ i,((NativeHeadSelect.resetState a).stacks i).length≤B := by
  intro i
  by_cases hi : i∈NativeHeadSelect.changed
  · simp [NativeHeadSelect.resetState,BankRoutines.clearBankStacks,hi]
  · simpa [NativeHeadSelect.resetState,BankRoutines.clearBankStacks,hi] using ha i

theorem reset_space (a : State 40 896) (B : ℕ)
    (ha : ∀ i,(a.stacks i).length≤B) :
    ∀ q z,q≤NativeHeadSelect.resetCost a →
      Trace (compiled NativeHeadSelect.reset 858 867) q
        (a.withPC (some (compiled NativeHeadSelect.reset 858 867).entry)) z →
      ∀ i,(z.stacks i).length≤B := by
  let middle : State 40 896 := ⟨readRegs a.regs 0 1 none,clearStacks 880 a.stacks⟩
  have first := BankRoutines.clear_call_eval (880:Fin 896) (0:Fin 40) 1 a.regs a.stacks
  have rest := BankRoutines.clear_eval (880:Fin 896) (0:Fin 40) 1 NativeHeadSelect.changed
    (by decide) middle.regs middle.stacks (by simp [middle])
  have hf := HighQuerySpace.clear_bound (880:Fin 896) (0:Fin 40) 1 a B ha 858 867
  have hr := HighQuerySpace.clear_bank_bound (880:Fin 896) (0:Fin 40) 1 NativeHeadSelect.changed
    (by decide) middle (by simp [middle]) B
    (HighQuerySpace.clear_state_bound 880 0 1 a B ha) 858 867
  exact StructuredSpace.sequence_stack_bound first rest 858 867 hf hr _ _ _
    (compiled_site NativeHeadSelect.reset 858 867)

/-- The only growing part is a five-stack local scan with ambient input
length≤P. Its11P+6 transient allowance is independent of caller envelope B. -/
theorem command_space (a : State 40 896) (P B : ℕ)
    (he : ∀ i∈NativeHeadSelect.changed,a.stacks i=[])
    (hlen : (a.stacks 670).length=(a.stacks 858).length)
    (hsize : (a.stacks 670).length≤P) (hlocal : 11*P+6≤B)
    (ha : ∀ i,(a.stacks i).length≤B) :
    ∀ q z,q≤20*(a.stacks 670).length+3*Restriction.highCount (a.stacks 670)+16 →
      Trace (compiled NativeHeadSelect.command 858 867) q
        (a.withPC (some (compiled NativeHeadSelect.command 858 867).entry)) z →
      ∀ i,(z.stacks i).length≤B := by
  have h880 : a.stacks 880=[] := he 880 (by decide)
  let middle : State 40 896 := ⟨readRegs a.regs 0 1 none,copyStacks 858 878 a.stacks⟩
  have first : Eval (NativeHeadSelect.copy 858 878) (7*(a.stacks 858).length+5) a middle :=
    .call _ (ListRegisterProgram.copy_run 858 878 880 0 1 (by decide) (by decide)
      (by decide) (by decide) a.regs a.stacks h880)
  have second : Eval (NativeHeadSelect.copy 670 879) (7*(a.stacks 670).length+5)
      middle (NativeHeadSelect.copied a) := by
    apply Eval.call
    simpa [middle, NativeHeadSelect.copied, copyStacks, h880] using
      ListRegisterProgram.copy_run (670:Fin 896) 879 880 (0:Fin 40) 1
        (by decide) (by decide) (by decide) (by decide)
        middle.regs middle.stacks (by simp [middle,copyStacks,h880])
  have hf : ∀ q z,q≤7*(a.stacks 858).length+5 →
      Trace (compiled (NativeHeadSelect.copy 858 878) 858 867) q
        (a.withPC (some (compiled (NativeHeadSelect.copy 858 878) 858 867).entry)) z →
      ∀ i,(z.stacks i).length≤B := by
    cases first with
    | call p tr =>
      apply StructuredSpace.call_stack_bound _ _ _ _
        (compiled_site (NativeHeadSelect.copy 858 878) 858 867) tr
      intro q z _ hz
      exact CopySpace.copyProgram_no_growth 858 878 880 0 1 (by decide) (by decide)
        (by decide) rfl (he 878 (by decide)) h880 ha hz
  have hm : ∀ i,(middle.stacks i).length≤B := hf _ _ le_rfl (compiled_trace first 858 867)
  have hs : ∀ q z,q≤7*(a.stacks 670).length+5 →
      Trace (compiled (NativeHeadSelect.copy 670 879) 858 867) q
        (middle.withPC (some (compiled (NativeHeadSelect.copy 670 879) 858 867).entry)) z →
      ∀ i,(z.stacks i).length≤B := by
    cases second with
    | call p tr =>
      apply StructuredSpace.call_stack_bound _ _ _ _
        (compiled_site (NativeHeadSelect.copy 670 879) 858 867) tr
      intro q z _ hz
      exact CopySpace.copyProgram_no_growth 670 879 880 0 1 (by decide) (by decide)
        (by decide) rfl (by simp [middle,copyStacks,he 879 (by decide)])
        (by simp [middle,copyStacks,h880]) hm hz
  have hc : ∀ i,((NativeHeadSelect.copied a).stacks i).length≤B :=
    hs _ _ le_rfl (compiled_trace second 858 867)
  have hp : projectState NativeHeadSelect.regs NativeHeadSelect.stackMap (NativeHeadSelect.copied a) =
      HeadSelect.state ((NativeHeadSelect.copied a).regs ∘ NativeHeadSelect.regs)
        (a.stacks 670) (a.stacks 858) [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [NativeHeadSelect.copied,NativeHeadSelect.stackMap,
        copyStacks,he 867 (by decide),he 868 (by decide),he 877 (by decide),
        he 878 (by decide),he 879 (by decide)]
  obtain ⟨rf,localEval⟩ := HeadSelect.command_eval
    ((NativeHeadSelect.copied a).regs ∘ NativeHeadSelect.regs) (a.stacks 670) (a.stacks 858) hlen
  have localTrace := compiled_halt_trace localEval 0 3
  have hcount : Restriction.highCount (a.stacks 670)≤(a.stacks 670).length :=
    List.length_filter_le _ _
  have localBound : ∀ q z,q≤6*(a.stacks 670).length+3*Restriction.highCount (a.stacks 670)+5+1 →
      Trace HeadSelect.program q
        ((HeadSelect.state ((NativeHeadSelect.copied a).regs ∘ NativeHeadSelect.regs)
          (a.stacks 670) (a.stacks 858) [] [] []).withPC (some HeadSelect.program.entry)) z →
      ∀ i,(z.stacks i).length≤B := by
    have hi : dataBits ((HeadSelect.state ((NativeHeadSelect.copied a).regs ∘ NativeHeadSelect.regs)
        (a.stacks 670) (a.stacks 858) [] [] []).withPC (some HeadSelect.program.entry))≤2*P := by
      simp [dataBits,stackBits,HeadSelect.state,Fin.sum_univ_succ]
      omega
    intro q z hq hz i
    have ht := StructuredSpace.local_stack_bound HeadSelect.program (steps:=9*P+6) hi
      q z (by omega) hz i
    omega
  have hlast := HighQuerySpace.lifted_call_bound HeadSelect.program NativeHeadSelect.regs
    NativeHeadSelect.stackMap (Fin.castAdd_injective _ _) (by decide)
    (NativeHeadSelect.copied a) _ _ hp _ B localTrace localBound hc 858 867
  rw [←hp] at localTrace
  have last := eval_call_from_state HeadSelect.program NativeHeadSelect.regs NativeHeadSelect.stackMap
    (NativeHeadSelect.copied a) (Fin.castAdd_injective _ _) (by decide) localTrace
  have tail := StructuredSpace.sequence_stack_bound second last 858 867 hs hlast _ _ _
    (compiled_site (.seq (NativeHeadSelect.copy 670 879) NativeHeadSelect.select) 858 867)
  have whole := StructuredSpace.sequence_stack_bound first (second.seq last) 858 867 hf tail _ _ _
    (compiled_site NativeHeadSelect.command 858 867)
  obtain ⟨out,canonical⟩ := NativeHeadSelect.command_eval a he hlen
  have htime := StreamResources.eval_steps_eq 858 867 (first.seq (second.seq last)) canonical
  simpa only [NativeHeadSelect.command, NativeHeadSelect.select, StructuredCalls.compiled,
    htime] using whole

/-- Paid reset and selection share one caller bound, including every final
halt and every old output discarded before a repeated head setup. -/
theorem prepare_trace_space (a : State 40 896) (P B : ℕ)
    (hlen : (a.stacks 670).length=(a.stacks 858).length)
    (hsize : (a.stacks 670).length≤P) (hlocal : 11*P+6≤B)
    (ha : ∀ i,(a.stacks i).length≤B) :
    ∃ steps rf,Trace NativeHeadSelect.prepareProgram steps
      (a.withPC (some NativeHeadSelect.prepareProgram.entry))
      ((NativeHeadSelect.result (NativeHeadSelect.resetState a) rf).withPC none) ∧
      steps≤37*B+41 ∧
      ∀ (q : ℕ) z, Nat.le q steps → Trace NativeHeadSelect.prepareProgram q
        (a.withPC (some NativeHeadSelect.prepareProgram.entry)) z →
        ∀ i,(z.stacks i).length≤B := by
  have hm := NativeHeadSelect.reset_frame a 670 (by decide)
  have he := NativeHeadSelect.reset_frame a 858 (by decide)
  have hclean : ∀ i∈NativeHeadSelect.changed,(NativeHeadSelect.resetState a).stacks i=[] :=
    fun i hi => BankRoutines.clearBankStacks_mem i NativeHeadSelect.changed a.stacks hi
  have hlen' : ((NativeHeadSelect.resetState a).stacks 670).length=
      ((NativeHeadSelect.resetState a).stacks 858).length := by simpa only [hm,he] using hlen
  obtain ⟨rf,hs⟩ := NativeHeadSelect.command_eval (NativeHeadSelect.resetState a) hclean hlen'
  have heval := (NativeHeadSelect.reset_eval a).seq hs
  have hf := reset_space a B ha
  have hg := command_space (NativeHeadSelect.resetState a) P B hclean hlen'
    (by simpa only [hm] using hsize) hlocal (reset_bound a B ha)
  have hp := StructuredSpace.sequence_stack_bound (NativeHeadSelect.reset_eval a) hs
    858 867 hf hg _ _ _ (compiled_site NativeHeadSelect.prepare 858 867)
  have bound := StructuredSpace.compiled_halt_stack_bound heval 858 867 hp
  obtain ⟨n,r,htr,htime,_⟩ := NativeHeadSelect.prepare_trace_space a B hlen ha
  have hsteps : n=NativeHeadSelect.resetCost a+
      (20*((NativeHeadSelect.resetState a).stacks 670).length+
        3*Restriction.highCount ((NativeHeadSelect.resetState a).stacks 670)+16)+1 :=
    StreamResources.halted_trace_steps_eq htr (compiled_halt_trace heval 858 867) rfl rfl
  refine ⟨_,rf,compiled_halt_trace heval 858 867,?_,bound⟩
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSelectionSpace
