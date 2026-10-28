import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedCleanup
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendSources
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendMask
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryFrontend
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryAccepted
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendUniform

/-! The original actual marked-scope/high-mask/parameter frontend is lifted
into the shared leaf ABI. Upper caller words and the marked mass collector
are retained; the lower workspace is reclaimed by an actual cleanup program. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafParametersProgram

def localProgram (k : ℕ) := compiled (LeafProgram.Query.markedFrontend k) 321 338
def command (k : ℕ) : Code := .call (ProgramLinking.liftProgram (localProgram k) id stackMap)
def program (k : ℕ) := compiled (command k) 321 338
noncomputable def budget (q : LeafQueryFrontend.Query) (k : ℕ) : ℕ :=
  10*q.index.length+q.inputBudget k+12

/-- Reference staging preserves a physical input cap, apart from its one-bit
flag. This cap is independent of retained upper caller words. -/
theorem markedInput_bound (a : LeafProgram.Query.Data) (bound : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ bound)
    (h699 : a.stacks 699=[]) (h705 : a.stacks 705=[]) (h706 : a.stacks 706=[]) :
    ∀ i, ((LeafProgram.Query.markedInput a).stacks i).length ≤ bound+1 := by
  intro i
  by_cases h0 : i=699
  · subst i
    rw [LeafProgram.Query.markedInput_temporary]
    simp
  by_cases h5 : i=705
  · subst i
    rw [LeafProgram.Query.markedInput_index a h699 h705,List.length_reverse]
    exact (hb 321).trans (Nat.le_succ _)
  by_cases h6 : i=706
  · subst i
    rw [LeafProgram.Query.markedInput_flag a h706]
    simp
  rw [LeafProgram.Query.markedInput_frame a i h0 h5 h6]
  exact (hb i).trans (Nat.le_succ _)

theorem unmarkedInput_bound (a : LeafProgram.Query.Data) (bound : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ bound)
    (h705 : a.stacks 705=[]) (h706 : a.stacks 706=[]) :
    ∀ i, ((LeafProgram.Query.unmarkedInput a).stacks i).length ≤ bound+1 := by
  intro i
  by_cases h5 : i=705
  · subst i
    rw [LeafProgram.Query.unmarkedInput_index a h705]
    simp
  by_cases h6 : i=706
  · subst i
    rw [LeafProgram.Query.unmarkedInput_flag a h706]
    simp
  rw [LeafProgram.Query.unmarkedInput_frame a i h5 h6]
  exact (hb i).trans (Nat.le_succ _)

private theorem marked_time_le (q : LeafQueryFrontend.Query) (k : ℕ)
    (a b : LeafProgram.Query.Data) (n : ℕ) (hv : q.Valid)
    (hc : LeafProgram.Query.CleanWork a) (hs : LeafProgram.Query.Sources q a)
    (hm : q.mark.isSome=true) (href : a.stacks 321=q.index.reverse)
    (he : Eval (LeafProgram.Query.markedFrontend k) n a b) : n+2 ≤ budget q k := by
  have hready := LeafProgram.Query.marked_ready q a hc hs hm href
  have hempty := LeafProgram.Query.marked_outputs_empty a hc
  obtain ⟨nf,bf,hfront,hbound⟩ := LeafQueryFrontend.frontend_eval_input_bound q k
    (LeafProgram.Query.markedInput a) hv hready hempty
  have hmark := LeafProgram.Query.markInput_eval a (hc 698 (by decide) (by decide))
    (hc 699 (by decide) (by decide))
  have hother := hmark.seq hfront
  have htime := SubexpPrimeProgram.eval_steps_unique he hother 321 338
  rw [href,List.length_reverse] at htime
  dsimp [budget]
  omega

/-- Actual marked frontend execution and input-dependent time do not require
a bound on suspended collector or caller words. -/
theorem command_eval (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark.isSome=true)
    (href : a.stacks 321=q.index.reverse) :
    ∃ steps b tau l w,
      Eval (command k) steps a (result a b) ∧
      steps+1 ≤ budget q k ∧
      BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 704=List.replicate q.rows.length true ∧
      b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows ∧
      b.stacks 338=LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 719=q.forward ∧ b.stacks 134=q.forward.map Bool.not ∧
      LeafQueryFrontend.Exported (Execute.guardedModel (q.input k) l) b ∧
      BinaryArithmetic.toNat (b.stacks 141)=2*(Execute.guardedModel (q.input k) l).val 3*
        (8*(Execute.guardedModel (q.input k) l).val 21)^(2*(Execute.guardedModel (q.input k) l).val 29) ∧
      projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) w ∧
      Circuit.Shape (Execute.guardedModel (q.input k) l) w ∧
      (b.regs 8=true ↔ Guard (q.input k)) ∧ LeafQueryFrontend.emptyRange b 417 680 ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) →
        i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 → i≠705 → i≠706 → i≠699 →
        (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks (stackMap i)) := by
  have href' : (project a).stacks 321=q.index.reverse := href
  obtain ⟨n,b,counted,prepared,beforeClean,tau,l,w,he,_,ht,h704,h718,h338,h719,h134,
      hex,h141,hbank,hshape,hguard,hclean,hframe⟩ :=
    LeafProgram.Query.marked_frontend_eval q k (project a) hv hc hs hm href'
  have hn := marked_time_le q k (project a) b n hv hc hs hm href' he
  have htlocal : Trace (localProgram k) (n+1)
      ((project a).withPC (some (localProgram k).entry)) (b.withPC none) :=
    compiled_halt_trace he 321 338
  have hev := eval_call_from_state (localProgram k) id stackMap a
    Function.injective_id (Fin.castAdd_injective _ _) htlocal
  exact ⟨n+1,b,tau,l,w,hev,by omega,ht,h704,h718,h338,h719,h134,
    hex,h141,hbank,hshape,hguard,hclean,hframe⟩

/-- Full native frontend outputs, current marked scopes and high mask, and
all-prefix storage belong to the same actual lifted execution. The physical
local input cap is separate from retained upper caller stacks. -/
theorem run (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark.isSome=true)
    (href : a.stacks 321=q.index.reverse) (localCap callerBound : ℕ)
    (hinput : ∀ i : Fin 768, ((project a).stacks i).length ≤ localCap)
    (hcaller : ∀ i, (a.stacks i).length ≤ callerBound) :
    ∃ steps b tau l w,
      Trace (program k) steps (a.withPC (some (program k).entry)) ((result a b).withPC none) ∧
      steps ≤ budget q k ∧
      BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 704=List.replicate q.rows.length true ∧
      b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows ∧
      b.stacks 338=LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 719=q.forward ∧ b.stacks 134=q.forward.map Bool.not ∧
      LeafQueryFrontend.Exported (Execute.guardedModel (q.input k) l) b ∧
      BinaryArithmetic.toNat (b.stacks 141)=2*(Execute.guardedModel (q.input k) l).val 3*
        (8*(Execute.guardedModel (q.input k) l).val 21)^(2*(Execute.guardedModel (q.input k) l).val 29) ∧
      projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) w ∧
      Circuit.Shape (Execute.guardedModel (q.input k) l) w ∧
      (b.regs 8=true ↔ Guard (q.input k)) ∧ LeafQueryFrontend.emptyRange b 417 680 ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) →
        i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 → i≠705 → i≠706 → i≠699 →
        (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks (stackMap i)) ∧
      ∀ (t : ℕ) z, t ≤ steps → Trace (program k) t (a.withPC (some (program k).entry)) z →
        ∀ i, (z.stacks i).length ≤ max (768*localCap+budget q k) callerBound := by
  have href' : (project a).stacks 321=q.index.reverse := href
  obtain ⟨n,b,counted,prepared,beforeClean,tau,l,w,he,_,ht,h704,h718,h338,h719,h134,
      hex,h141,hbank,hshape,hguard,hclean,hframe⟩ :=
    LeafProgram.Query.marked_frontend_eval q k (project a) hv hc hs hm href'
  have hn := marked_time_le q k (project a) b n hv hc hs hm href' he
  have htlocal : Trace (localProgram k) (n+1)
      ((project a).withPC (some (localProgram k).entry)) (b.withPC none) :=
    compiled_halt_trace he 321 338
  have hin : dataBits ((project a).withPC (some (localProgram k).entry))≤768*localCap :=
    StreamResources.dataBits_le_mul _ (by simpa using hinput)
  have hp : ∀ t z, t ≤ n+1 → Trace (localProgram k) t
      ((project a).withPC (some (localProgram k).entry)) z →
      ∀ i, (z.stacks i).length ≤ max (768*localCap+budget q k) callerBound := by
    intro t z ht hz i
    exact (StructuredSpace.local_stack_bound (localProgram k) (steps:=budget q k) hin
      t z (by omega) hz i).trans (Nat.le_max_left _ _)
  have hev := eval_call_from_state (localProgram k) id stackMap a
    Function.injective_id (Fin.castAdd_injective _ _) htlocal
  have hcall := HighQuerySpace.lifted_call_bound (localProgram k) id stackMap
    Function.injective_id (Fin.castAdd_injective _ _) a (project a) b rfl _
    (max (768*localCap+budget q k) callerBound) htlocal hp
    (fun i => (hcaller i).trans (Nat.le_max_right _ _)) 321 338
  refine ⟨n+1+1,b,tau,l,w,compiled_halt_trace hev 321 338,by omega,
    ht,h704,h718,h338,h719,h134,hex,h141,hbank,hshape,hguard,hclean,hframe,?_⟩
  exact StructuredSpace.compiled_halt_stack_bound hev 321 338 hcall

private theorem lifted_command_run_space {r s R S : ℕ}
    (c : Cmd r s) (input output : Fin s)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (callerInput callerOutput : Fin S) (a : State R S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    {n : ℕ} {b : State r s}
    (he : Eval c n (projectState register stack a) b)
    (localCap callerBound timeBound : ℕ)
    (hlocal : ∀ i, ((projectState register stack a).stacks i).length ≤ localCap)
    (hcaller : ∀ i, (a.stacks i).length ≤ callerBound)
    (htime : n + 1 ≤ timeBound) :
    Eval (liftCommand c input output register stack) (n + 1) a
        (embedState register stack a b) ∧
      ∀ q z, q ≤ n + 1 →
        Trace (compiled (liftCommand c input output register stack) callerInput callerOutput) q
          (a.withPC (some (compiled (liftCommand c input output register stack)
            callerInput callerOutput).entry)) z →
        ∀ i, (z.stacks i).length ≤ max (s * localCap + timeBound) callerBound := by
  have htlocal := compiled_halt_trace he input output
  have hin : dataBits ((projectState register stack a).withPC
      (some (compiled c input output).entry)) ≤ s * localCap :=
    StreamResources.dataBits_le_mul _ hlocal
  have hp : ∀ q z, q ≤ n + 1 → Trace (compiled c input output) q
      ((projectState register stack a).withPC (some (compiled c input output).entry)) z →
      ∀ i, (z.stacks i).length ≤ max (s * localCap + timeBound) callerBound := by
    intro q z hq hz i
    exact (StructuredSpace.local_stack_bound (compiled c input output)
      (steps := timeBound) hin q z (hq.trans htime) hz i).trans
        (Nat.le_max_left _ _)
  have hev := eval_liftCommand_from_state c input output register stack a hr hs he
  have hcall := HighQuerySpace.lifted_call_bound (compiled c input output) register stack
    hr hs a _ _ rfl (n + 1) (max (s * localCap + timeBound) callerBound)
    htlocal hp (fun i => (hcaller i).trans (Nat.le_max_right _ _))
    callerInput callerOutput
  exact ⟨hev, hcall⟩

def acceptedLocalCommand (k : ℕ) : LeafProgram.Query.Code :=
  .seq LeafProgram.Query.noMarkInput (LeafQueryFrontend.frontend k)
def acceptedLocalProgram (k : ℕ) := compiled (acceptedLocalCommand k) 700 338
def acceptedCommand (k : ℕ) : Code :=
  .call (ProgramLinking.liftProgram (acceptedLocalProgram k) id stackMap)
def acceptedProgram (k : ℕ) := compiled (acceptedCommand k) 700 338
noncomputable def acceptedBudget (q : LeafQueryFrontend.Query) (k : ℕ) := q.inputBudget k+5

/-- The unmarked native execution also has a source-dependent time bound
without restricting suspended collector words. -/
theorem accepted_command_eval (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark=none)
    (hindex : q.index=[false]) :
    ∃ steps b tau l w,
      Eval (acceptedCommand k) steps a (result a b) ∧
      steps+1 ≤ acceptedBudget q k ∧
      BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 704=List.replicate q.rows.length true ∧
      b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows ∧
      b.stacks 338=LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 719=q.forward ∧ b.stacks 134=q.forward.map Bool.not ∧
      LeafQueryFrontend.Exported (Execute.guardedModel (q.input k) l) b ∧
      BinaryArithmetic.toNat (b.stacks 141)=2*(Execute.guardedModel (q.input k) l).val 3*
        (8*(Execute.guardedModel (q.input k) l).val 21)^(2*(Execute.guardedModel (q.input k) l).val 29) ∧
      projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) w ∧
      Circuit.Shape (Execute.guardedModel (q.input k) l) w ∧
      (b.regs 8=true ↔ Guard (q.input k)) ∧ LeafQueryFrontend.emptyRange b 417 680 ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) →
        i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 → i≠705 → i≠706 → i≠699 →
        (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks (stackMap i)) := by
  have hready := LeafProgram.Query.accepted_ready q (project a) hc hs hm hindex
  have hempty := LeafProgram.Query.accepted_outputs_empty (project a) hc
  obtain ⟨n,b,counted,prepared,beforeClean,tau,l,w,he,_,ht,h704,h718,h338,h719,h134,
      hex,h141,hbank,hshape,hguard,hclean,hframe⟩ :=
    LeafQueryFrontend.frontend_eval q k (LeafProgram.Query.unmarkedInput (project a))
      hv hready hempty
  have hn := LeafQueryFrontend.frontend_time_le q k hv hready hempty he
  have hwhole := (LeafProgram.Query.noMarkInput_eval (project a)).seq he
  have hev := eval_liftCommand_from_state (acceptedLocalCommand k) 700 338 id stackMap a
    Function.injective_id (Fin.castAdd_injective _ _) hwhole
  refine ⟨3+n+1,b,tau,l,w,?_,by dsimp [acceptedBudget]; omega,
    ht,h704,h718,h338,h719,h134,hex,h141,hbank,hshape,hguard,hclean,?_⟩
  · simpa only [acceptedCommand,acceptedLocalProgram,result] using hev
  intro i hi h134 h141 h338 h704 h718 h719 h705 h706 _ hd
  exact (hframe i hi h134 h141 h338 h704 h718 h719 hd).trans
    (LeafProgram.Query.unmarkedInput_frame (project a) i h705 h706)

/-- The final unmarked count regenerates its own scopes and high set from the
current source rows, using the same actual frontend as each marked query. -/
theorem accepted_run (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark=none)
    (hindex : q.index=[false]) (localCap callerBound : ℕ)
    (hinput : ∀ i : Fin 768, ((project a).stacks i).length ≤ localCap)
    (hcaller : ∀ i, (a.stacks i).length ≤ callerBound) :
    ∃ steps b tau l w,
      Trace (acceptedProgram k) steps (a.withPC (some (acceptedProgram k).entry)) ((result a b).withPC none) ∧
      steps ≤ acceptedBudget q k ∧
      BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 704=List.replicate q.rows.length true ∧
      b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows ∧
      b.stacks 338=LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 719=q.forward ∧ b.stacks 134=q.forward.map Bool.not ∧
      LeafQueryFrontend.Exported (Execute.guardedModel (q.input k) l) b ∧
      BinaryArithmetic.toNat (b.stacks 141)=2*(Execute.guardedModel (q.input k) l).val 3*
        (8*(Execute.guardedModel (q.input k) l).val 21)^(2*(Execute.guardedModel (q.input k) l).val 29) ∧
      projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) w ∧
      Circuit.Shape (Execute.guardedModel (q.input k) l) w ∧
      (b.regs 8=true ↔ Guard (q.input k)) ∧ LeafQueryFrontend.emptyRange b 417 680 ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) →
        i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 → i≠705 → i≠706 → i≠699 →
        (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks (stackMap i)) ∧
      ∀ (t : ℕ) z, t ≤ steps →
        Trace (acceptedProgram k) t (a.withPC (some (acceptedProgram k).entry)) z →
        ∀ i, (z.stacks i).length ≤ max (768*localCap+acceptedBudget q k) callerBound := by
  have hready := LeafProgram.Query.accepted_ready q (project a) hc hs hm hindex
  have hempty := LeafProgram.Query.accepted_outputs_empty (project a) hc
  obtain ⟨n,b,counted,prepared,beforeClean,tau,l,w,he,_,ht,h704,h718,h338,h719,h134,
      hex,h141,hbank,hshape,hguard,hclean,hframe⟩ :=
    LeafQueryFrontend.frontend_eval q k (LeafProgram.Query.unmarkedInput (project a))
      hv hready hempty
  have hn := LeafQueryFrontend.frontend_time_le q k hv hready hempty he
  have hwhole := (LeafProgram.Query.noMarkInput_eval (project a)).seq he
  have hrun := lifted_command_run_space (acceptedLocalCommand k) 700 338 id stackMap
    700 338 a Function.injective_id (Fin.castAdd_injective _ _) hwhole
    localCap callerBound (acceptedBudget q k) hinput hcaller
    (by dsimp [acceptedBudget]; omega)
  have hev : Eval (acceptedCommand k) (3+n+1) a (result a b) := by
    simpa only [acceptedCommand,acceptedLocalProgram,result] using hrun.1
  have hcall : ∀ t z, t ≤ 3+n+1 →
      Trace (acceptedProgram k) t (a.withPC (some (acceptedProgram k).entry)) z →
      ∀ i, (z.stacks i).length ≤ max (768*localCap+acceptedBudget q k) callerBound := by
    simpa only [acceptedProgram,acceptedCommand,acceptedLocalProgram] using hrun.2
  refine ⟨3+n+1+1,b,tau,l,w,compiled_halt_trace hev 700 338,
    by dsimp [acceptedBudget]; omega,ht,h704,h718,h338,h719,h134,hex,h141,hbank,
    hshape,hguard,hclean,?_,?_⟩
  · intro i hi h134 h141 h338 h704 h718 h719 h705 h706 _ hd
    exact (hframe i hi h134 h141 h338 h704 h718 h719 hd).trans
      (LeafProgram.Query.unmarkedInput_frame (project a) i h705 h706)
  · exact StructuredSpace.compiled_halt_stack_bound hev 700 338 hcall

/-- Physical protected collector words are not frontend outputs. -/
theorem collector_frame (a : Data) (b : LeafProgram.Query.Data)
    (hframe : ∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) →
      i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 → i≠705 → i≠706 → i≠699 →
      (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks (stackMap i)) :
    (result a b).stacks 320=a.stacks 320 ∧ (result a b).stacks 322=a.stacks 322 := by
  constructor
  · rw [show (320 : Fin 896)=stackMap 320 from rfl,result_stack]
    exact hframe 320 (Or.inl (by decide)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)
  · rw [show (322 : Fin 896)=stackMap 322 from rfl,result_stack]
    exact hframe 322 (Or.inl (by decide)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)

/-- The concrete return collector's retained words survive the actual
frontend result. This includes immutable sources and every caller bank. -/
theorem result_kept_frame (a : Data) (b : LeafProgram.Query.Data)
    (hframe : ∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) →
      i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 → i≠705 → i≠706 → i≠699 →
      (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks (stackMap i)) :
    ∀ i, HashMarkedReturn.kept i=true → (result a b).stacks i=a.stacks i := by
  intro i hk
  by_cases hi : i.val<768
  · let j : Fin 768 := ⟨i.val,hi⟩
    have hij : i=stackMap j := rfl
    have hv : j.val=320 ∨ j.val=322 ∨ j.val=700 ∨ j.val=701 ∨
        j.val=707 ∨ j.val=708 ∨ j.val=709 ∨ 744 ≤ j.val := by
      simp only [HashMarkedReturn.kept,decide_eq_true_eq,Fin.ext_iff,
        Fin.coe_ofNat_eq_mod] at hk
      dsimp [j]
      omega
    rw [hij,result_stack]
    apply hframe j (by omega)
    all_goals try (intro he; have hh := congrArg Fin.val he; norm_num at hh; omega)
    intro x he
    have hh := congrArg Fin.val he
    fin_cases x <;> norm_num [Exports.destination] at hh <;> omega
  · exact result_upper_frame a b i (by omega)

/-- Exact kept-word frame for any actual marked frontend execution, obtained
from its concrete evaluated output by deterministic execution uniqueness. -/
theorem command_kept_frame (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Data)
    (steps : ℕ) (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark.isSome=true)
    (href : a.stacks 321=q.index.reverse) (he : Eval (command k) steps a b) :
    ∀ i, HashMarkedReturn.kept i=true → b.stacks i=a.stacks i := by
  obtain ⟨n,c,tau,l,w,hec,_,_,_,_,_,_,_,_,_,_,_,_,_,hf⟩ :=
    command_eval q k a hv hc hs hm href
  have hb := SubexpPrimeProgram.eval_result_unique he hec 321 338
  rw [hb]
  exact result_kept_frame a c hf

/-- The accepted history-only frontend preserves the same concrete retained
words before its final count is installed on788. -/
theorem accepted_command_kept_frame (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Data)
    (steps : ℕ) (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark=none)
    (hindex : q.index=[false]) (he : Eval (acceptedCommand k) steps a b) :
    ∀ i, HashMarkedReturn.kept i=true → b.stacks i=a.stacks i := by
  obtain ⟨n,c,tau,l,w,hec,_,_,_,_,_,_,_,_,_,_,_,_,_,hf⟩ :=
    accepted_command_eval q k a hv hc hs hm hindex
  have hb := SubexpPrimeProgram.eval_result_unique he hec 700 338
  rw [hb]
  exact result_kept_frame a c hf

theorem cleaned_cleanWork (a : Data) : LeafProgram.Query.CleanWork (project (cleaned a)) := by
  rw [cleaned,project_result]
  exact LeafProgram.Query.cleaned_cleanWork (project a)

theorem cleaned_sources (q : LeafQueryFrontend.Query) (a : Data)
    (h : LeafProgram.Query.Sources q (project a)) :
    LeafProgram.Query.Sources q (project (cleaned a)) := by
  rw [cleaned,project_result]
  exact LeafProgram.Query.cleaned_sources q (project a) h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
