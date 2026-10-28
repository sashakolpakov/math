import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace

/-! Separate the retained caller envelope from each physical local input cap.
The local transient bound is never recycled as the next iteration's input. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace

open BitProgram StructuredCalls StackRoutines
open HighQueryAdapter

theorem clear_bound {r s : ℕ} (src : Fin s) (value present : Fin r)
    (a : State r s) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound)
    (input output : Fin s) :
    ∀ (q : ℕ) z, q ≤ 2 * (a.stacks src).length + 3 →
      Trace (compiled (.call (clearProgram src value present)) input output) q
        (a.withPC (some (compiled (.call (clearProgram src value present)) input output).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
  have ht : Trace (clearProgram src value present) (2*(a.stacks src).length+3)
      (a.withPC (some (clearProgram src value present).entry))
      ((⟨readRegs a.regs value present none,clearStacks src a.stacks⟩ : State r s).withPC none) :=
    ListRegisterProgram.clear_run src value present a.regs a.stacks
  apply StructuredSpace.call_stack_bound _ _ _ _ (compiled_site (.call (clearProgram src value present)) input output) ht
  intro q z _ hz i
  exact (DisjointReuse.SparseDFSBoundarySpace.clearProgram_stack_length_le src value present hz i).trans (hb i)

theorem clear_state_bound {r s : ℕ} (src : Fin s) (value present : Fin r)
    (a : State r s) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ i, ((⟨readRegs a.regs value present none,clearStacks src a.stacks⟩ : State r s).stacks i).length≤bound := by
  intro i
  by_cases hi : i=src
  · subst i; simp
  · simpa only [clearStacks_frame src i a.stacks hi] using hb i

theorem clear_bank_bound {r s : ℕ} (tmp : Fin s) (value present : Fin r)
    (ports : List (Fin s)) (hp : ports.Nodup) (a : State r s)
    (hempty : a.stacks tmp=[]) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound)
    (input output : Fin s) :
    ∀ (q : ℕ) z,
      q ≤ 2 * (ports.map (fun i => (a.stacks i).length)).sum + 3 * ports.length + 3 →
      Trace (compiled (BankRoutines.clearCmd tmp value present ports) input output) q
        (a.withPC (some (compiled (BankRoutines.clearCmd tmp value present ports) input output).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
  induction ports generalizing a with
  | nil =>
      simpa only [BankRoutines.clearCmd,hempty,List.length_nil,List.map_nil,List.sum_nil,
        Nat.mul_zero,Nat.zero_add] using clear_bound tmp value present a bound hb input output
  | cons dst ports ih =>
      have hn := List.nodup_cons.mp hp
      let middle : State r s := ⟨readRegs a.regs value present none,clearStacks dst a.stacks⟩
      have hm : middle.stacks tmp=[] := by
        by_cases h : tmp=dst
        · subst tmp; simp [middle]
        · simpa only [middle,clearStacks_frame dst tmp a.stacks h] using hempty
      have hmap : ports.map (fun i => (middle.stacks i).length)=ports.map (fun i => (a.stacks i).length) := by
        apply List.map_congr_left
        intro i hi
        have h : i≠dst := by intro h; subst i; exact hn.1 hi
        exact congrArg List.length (clearStacks_frame dst i a.stacks h)
      have first := BankRoutines.clear_call_eval dst value present a.regs a.stacks
      have rest := BankRoutines.clear_eval tmp value present ports hn.2 middle.regs middle.stacks hm
      have hfirst := clear_bound dst value present a bound hb input output
      have hrest := ih hn.2 middle hm (clear_state_bound dst value present a bound hb)
      have htotal := StructuredSpace.sequence_stack_bound first rest input output hfirst hrest
        _ _ _ (compiled_site (.seq (.call (clearProgram dst value present))
          (BankRoutines.clearCmd tmp value present ports)) input output)
      have ha : (⟨a.regs, a.stacks⟩ : State r s) = a := by cases a; rfl
      intro q z hq hz
      apply htotal q z
      · simp only [List.map_cons, List.sum_cons, List.length_cons, hmap,
          Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] at hq ⊢
        exact hq
      · rw [ha]
        change Trace
          (compiled (.seq (.call (clearProgram dst value present))
            (BankRoutines.clearCmd tmp value present ports)) input output) q
          (a.withPC (some (compiled (.seq (.call (clearProgram dst value present))
            (BankRoutines.clearCmd tmp value present ports)) input output).entry)) z
        simpa only [BankRoutines.clearCmd] using hz

theorem lifted_call_bound {r s l R S : ℕ}
    (p : Program r s l) (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (a : State R S) (d e : State r s) (hproject : projectState reg stk a=d)
    (steps bound : ℕ) (ht : Trace p steps (d.withPC (some p.entry)) (e.withPC none))
    (hlocal : ∀ (q : ℕ) z, q ≤ steps → Trace p q (d.withPC (some p.entry)) z →
      ∀ i, (z.stacks i).length≤bound)
    (hb : ∀ i, (a.stacks i).length≤bound) (input output : Fin S) :
    ∀ (q : ℕ) z, q ≤ steps →
      Trace (compiled (.call (ProgramLinking.liftProgram p reg stk)) input output) q
        (a.withPC (some (compiled (.call (ProgramLinking.liftProgram p reg stk)) input output).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
  have hstart : embedState reg stk a d=a := by rw [←hproject,embedState_project reg stk a hr hs]
  have he := eval_call_lifted p reg stk a hr hs ht
  rw [hstart] at he
  have hglobal := StructuredSpace.liftProgram_stack_bound p reg stk (a.withPC none) hr hs ht hlocal hb
  have hinit : ProgramLinking.embedCfg reg stk id none (a.withPC none) (d.withPC (some p.entry)) =
      a.withPC (some (ProgramLinking.liftProgram p reg stk).entry) := by
    change (embedState reg stk a d).withPC _ = _
    rw [hstart]
    rfl
  rw [hinit] at hglobal
  simp only [Nat.max_self] at hglobal
  cases he with
  | call routine ht =>
      exact StructuredSpace.call_stack_bound _ _ _ _ (compiled_site (.call (ProgramLinking.liftProgram p reg stk)) input output) ht hglobal

private theorem overlay_reset_bound (a : State 40 896) (bound : ℕ)
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ i, ((NativeOverlay.resetState a).stacks i).length≤bound := by
  intro i
  by_cases hi : i∈NativeOverlay.changed
  · simp [NativeOverlay.resetState,BankRoutines.clearBankStacks,hi]
  · simpa [NativeOverlay.resetState,BankRoutines.clearBankStacks,hi] using hb i

private theorem overlay_reset_space (a : State 40 896) (bound : ℕ)
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ (q : ℕ) z, q ≤ NativeOverlay.resetCost a →
      Trace (compiled NativeOverlay.reset 859 145) q
        (a.withPC (some (compiled NativeOverlay.reset 859 145).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
  let middle : State 40 896 := ⟨readRegs a.regs 0 1 none,clearStacks 875 a.stacks⟩
  have first := BankRoutines.clear_call_eval (875 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have rest := BankRoutines.clear_eval (875 : Fin 896) (0 : Fin 40) 1 NativeOverlay.changed
    (by decide) middle.regs middle.stacks (by simp [middle])
  have hfirst := clear_bound (875 : Fin 896) (0 : Fin 40) 1 a bound hb 859 145
  have hrest := clear_bank_bound (875 : Fin 896) (0 : Fin 40) 1 NativeOverlay.changed
    (by decide) middle (by simp [middle]) bound (clear_state_bound 875 0 1 a bound hb) 859 145
  exact StructuredSpace.sequence_stack_bound first rest 859 145 hfirst hrest
    _ _ _ (compiled_site NativeOverlay.reset 859 145)

/-- Caller words are charged once. The only local size cap is on actual
head/mask/baseline and the two preserved local context words. -/
theorem overlay_command_space (a : State 40 896) (localCap bound : ℕ)
    (he : ∀ i∈NativeOverlay.changed, a.stacks i=[])
    (hh : (a.stacks 859).length=OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length=(a.stacks 869).length)
    (hmask : (a.stacks 670).length≤localCap)
    (hu : (a.stacks 870).length≤localCap) (hv : (a.stacks 871).length≤localCap)
    (hlocal : 66*localCap+42≤bound)
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ (q : ℕ) z,
      q ≤ 7 * (a.stacks 859).length + 47 * (a.stacks 670).length + 42 →
      Trace (compiled NativeOverlay.command 859 145) q
        (a.withPC (some (compiled NativeOverlay.command 859 145).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
  have hp : projectState NativeOverlay.regMap NativeOverlay.stackMap a =
      Overlay.state (a.regs ∘ NativeOverlay.regMap) (a.stacks 859) (a.stacks 670)
        (a.stacks 869) (a.stacks 870) (a.stacks 871) [] [] [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [NativeOverlay.stackMap,
        he 145 (by simp [NativeOverlay.changed]),he 872 (by simp [NativeOverlay.changed]),
        he 873 (by simp [NativeOverlay.changed]),he 874 (by simp [NativeOverlay.changed]),
        he 875 (by simp [NativeOverlay.changed]),he 876 (by simp [NativeOverlay.changed]),
        he 877 (by simp [NativeOverlay.changed])]
  obtain ⟨rf,ht,hs⟩ := Overlay.trace_space (a.regs ∘ NativeOverlay.regMap)
    (a.stacks 859) (a.stacks 670) (a.stacks 869) (a.stacks 870) (a.stacks 871)
    hh hm localCap hmask hu hv
  exact lifted_call_bound Overlay.program NativeOverlay.regMap NativeOverlay.stackMap
    (Fin.castAdd_injective _ _) (by decide) a _ _ hp _ bound ht
    (fun q z hq hz i => (hs q z hq hz i).trans hlocal) hb 859 145

/-- Repeated candidate calls retain one polynomial envelope on every source
prefix, including paid cleanup of arbitrary old work words. -/
theorem overlay_trace_space (a : State 40 896) (localCap bound : ℕ)
    (hh : (a.stacks 859).length=OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length=(a.stacks 869).length)
    (hmask : (a.stacks 670).length≤localCap)
    (hu : (a.stacks 870).length≤localCap) (hv : (a.stacks 871).length≤localCap)
    (hlocal : 66*localCap+42≤bound)
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ steps rf, Trace NativeOverlay.prepareProgram steps
      (a.withPC (some NativeOverlay.prepareProgram.entry))
      ((NativeOverlay.result (NativeOverlay.resetState a) rf).withPC none) ∧
      steps ≤ 70 * bound + 70 ∧
      ∀ (q : ℕ) z, q ≤ steps → Trace NativeOverlay.prepareProgram q
        (a.withPC (some NativeOverlay.prepareProgram.entry)) z →
        ∀ i, (z.stacks i).length≤bound := by
  have hbits := NativeOverlay.reset_frame a 859 (by decide)
  have hmask' := NativeOverlay.reset_frame a 670 (by decide)
  have hbase := NativeOverlay.reset_frame a 869 (by decide)
  have hu' := NativeOverlay.reset_frame a 870 (by decide)
  have hv' := NativeOverlay.reset_frame a 871 (by decide)
  have he : ∀ i∈NativeOverlay.changed, (NativeOverlay.resetState a).stacks i=[] :=
    fun i hi => BankRoutines.clearBankStacks_mem i NativeOverlay.changed a.stacks hi
  have hh' : ((NativeOverlay.resetState a).stacks 859).length=
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.highCount ((NativeOverlay.resetState a).stacks 670) := by
    simpa only [hbits,hmask'] using hh
  have hm' : ((NativeOverlay.resetState a).stacks 670).length=((NativeOverlay.resetState a).stacks 869).length := by
    simpa only [hmask',hbase] using hm
  obtain ⟨rf,hs⟩ := NativeOverlay.command_eval (NativeOverlay.resetState a) he hh' hm'
  have hfirst := overlay_reset_space a bound hb
  have hsecond := overlay_command_space (NativeOverlay.resetState a) localCap bound he hh' hm'
    (by simpa only [hmask'] using hmask) (by simpa only [hu'] using hu)
    (by simpa only [hv'] using hv) hlocal (overlay_reset_bound a bound hb)
  have hex := (NativeOverlay.reset_eval a).seq hs
  have hp := StructuredSpace.sequence_stack_bound (NativeOverlay.reset_eval a) hs 859 145
    hfirst hsecond _ _ _ (compiled_site NativeOverlay.prepare 859 145)
  have hspace := StructuredSpace.compiled_halt_stack_bound hex 859 145 hp
  have hsum :
      (NativeOverlay.changed.map (fun i => ((clearStacks 875 a.stacks) i).length)).sum ≤
        7 * bound := by
    apply (List.sum_le_length_nsmul _ bound (by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      by_cases heq : i=875
      · subst i
        simp [clearStacks]
      · simpa [clearStacks,heq] using hb i)).trans_eq
    simp [NativeOverlay.changed]
  have hc : NativeOverlay.resetCost a≤16*bound+27 := by
    dsimp [NativeOverlay.resetCost]
    have := hb 875
    omega
  have htime : NativeOverlay.resetCost a+(7*((NativeOverlay.resetState a).stacks 859).length+
      47*((NativeOverlay.resetState a).stacks 670).length+42)+1≤70*bound+70 := by
    rw [hbits,hmask']
    have := hb 859
    have := hb 670
    omega
  exact ⟨_,rf,compiled_halt_trace hex 859 145,htime,hspace⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace
