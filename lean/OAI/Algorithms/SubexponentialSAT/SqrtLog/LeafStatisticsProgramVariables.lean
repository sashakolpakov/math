import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramPrimitives
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramSpec

namespace OAI.Algorithms

/-! Exact runtime accumulation of residual variable statistics. Each degree is
computed by scanning the serialized original scopes. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
def variableState (r : Fin 10 → Bool) (scopes : List (List ℕ))
    (v : ℕ) (mask master : List Bool) (t : Totals) : Data :=
  ⟨r, ![scopeBits scopes,unary scopes.length,unary v,[],[],[],[],[],[],[],[],[],[],
    mask,unary t.free,unary t.occurrence,unary t.incidences,unary t.uncovered,[],[],master]⟩

def countPorts : Fin 13 → Fin 21 := Fin.castAdd 8
theorem countPorts_injective : Function.Injective countPorts := Fin.castAdd_injective _ _
def countDegree : Code := .call (ProgramLinking.liftProgram
  SubexpIncidenceSlotProgram.program id countPorts)

theorem countDegree_eval (r : Fin 10 → Bool) (scopes : List (List ℕ))
    (v : ℕ) (mask master : List Bool) (t : Totals) :
    ∃ n rf, n ≤ SubexpIncidenceSlotProgram.budget scopes scopes.length v ∧
      Eval countDegree n (variableState r scopes v mask master t)
        ⟨rf,Function.update (variableState r scopes v mask master t).stacks 3
          (unary (degree scopes v+1))⟩ := by
  let a := variableState r scopes v mask master t
  have hp : projectState id countPorts a =
      SubexpIncidenceSlotProgram.idle r scopes scopes.length v [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨rf,n,hn,ht⟩ := SubexpIncidenceSlotProgram.program_run r scopes scopes.length v le_rfl
  have hd : SubexpIncidenceSlotProgram.degree scopes scopes.length v = degree scopes v := by
    simp [SubexpIncidenceSlotProgram.degree,degree,Subexp.IncidencePlanSpec.degree,
      Subexp.IncidencePlanSpec.incidentIndices]
  let b := SubexpIncidenceSlotProgram.idle rf scopes scopes.length v (unary (degree scopes v+1))
  rw [hd,←hp] at ht
  have he := eval_call_from_state SubexpIncidenceSlotProgram.program id countPorts a
    Function.injective_id countPorts_injective ht
  have hb : embedState id countPorts a b =
      (⟨rf,Function.update a.stacks 3 (unary (degree scopes v+1))⟩ : Data) := by
    apply embedState_eq_of_ports id countPorts a _ b Function.injective_id countPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h3 : i ≠ 3 := fun h => hi ⟨3,h.symm⟩
      simp [h3]
  change Eval countDegree n a (embedState id countPorts a b) at he
  rw [hb] at he
  exact ⟨n,rf,hn,he⟩

def neutralize : Code := .seq (peek 3)
  (.ite 1 (.base .skip) (.seq (pushTrue 3) (pushTrue 17)))

theorem neutralize_eval (a : Data) (d u : ℕ)
    (hd : a.stacks 3 = unary d) (hu : a.stacks 17 = unary u) :
    ∃ n rf, n ≤ 6 ∧ Eval neutralize n a
      ⟨rf,Function.update (Function.update a.stacks 3 (unary (max 1 d))) 17
        (unary (u+(if d=0 then 1 else 0)))⟩ := by
  cases d with
  | zero =>
    let b := peeked 3 a
    let c := pushedTrue 3 b
    let e := pushedTrue 17 c
    have hbranch : Eval (.ite 1 (.base .skip) (.seq (pushTrue 3) (pushTrue 17))) 5 b e :=
      Eval.ite_false (by simp [b,peeked,hd,unary,readRegs])
        ((pushTrue_eval 3 b).seq (pushTrue_eval 17 c))
    refine ⟨6,e.regs,by omega,?_⟩
    have heq : e = ⟨e.regs,Function.update (Function.update a.stacks 3 (unary (max 1 0))) 17
        (unary (u+(if 0=0 then 1 else 0)))⟩ := by
      apply congrArg (StructuredProgram.State.mk e.regs)
      funext i
      by_cases h17 : i=17
      · subst i; simp [c,b,pushedTrue,peeked,hu,unary,List.replicate_succ]
      by_cases h3 : i=3
      · subst i; simp [c,b,pushedTrue,peeked,hd,unary]
      · simp [c,b,pushedTrue,peeked,h17,h3]
    have h := (peek_eval 3 a).seq hbranch
    rw [heq] at h
    exact h
  | succ d =>
    let b := peeked 3 a
    have hbranch : Eval (.ite 1 (.base .skip) (.seq (pushTrue 3) (pushTrue 17))) 1 b b :=
      Eval.ite_true (by simp [b,peeked,hd,unary,readRegs,List.replicate_succ])
        (Eval.base (StructuredProgram.Eval.skip b))
    refine ⟨2,b.regs,by omega,?_⟩
    have heq : b = ⟨b.regs,Function.update (Function.update a.stacks 3 (unary (max 1 (d+1)))) 17
        (unary (u+(if d+1=0 then 1 else 0)))⟩ := by
      apply congrArg (StructuredProgram.State.mk b.regs)
      have hm : max 1 (d+1)=d+1 := by omega
      simp [←hd,←hu]
    have h := (peek_eval 3 a).seq hbranch
    rw [heq] at h
    exact h

def accumulateLow : Code := .seq (pushTrue 14) (.seq (pop 3)
  (.seq neutralize (.seq (copy 3 18 19) (.seq (transfer 3 16) maximum))))

theorem accumulateLow_eval (r : Fin 10 → Bool) (scopes : List (List ℕ))
    (v d : ℕ) (mask master : List Bool) (t : Totals) :
    ∃ n rf, n ≤ 30*(d+1)+30 ∧
      Eval accumulateLow n
        ⟨r,Function.update (variableState r scopes v mask master t).stacks 3 (unary (d+1))⟩
        (variableState rf scopes v mask master (t.add d)) := by
  let a : Data := ⟨r,Function.update (variableState r scopes v mask master t).stacks 3 (unary (d+1))⟩
  let b := pushedTrue 14 a
  let c := popped 3 b
  have hc3 : c.stacks 3 = unary d := by simp [c,b,a,popped,pushedTrue,unary,List.replicate_succ]
  have hc17 : c.stacks 17 = unary t.uncovered := by simp [c,b,a,popped,pushedTrue,variableState]
  obtain ⟨nn,rn,hnn,hen⟩ := neutralize_eval c d t.uncovered hc3 hc17
  let e : Data := ⟨rn,Function.update (Function.update c.stacks 3 (unary (max 1 d))) 17
    (unary (t.uncovered+(if d=0 then 1 else 0)))⟩
  let f := copied 3 18 e
  let g := transferred 3 16 f
  have he19 : e.stacks 19 = [] := by simp [e,c,b,a,popped,pushedTrue,variableState]
  have hcopy := copy_eval 3 18 19 e (by decide) (by decide) (by decide) he19
  have htransfer := transfer_eval 3 16 f (by decide)
  have hg18 : g.stacks 18 = unary (max 1 d) := by
    simp [g,f,e,c,b,a,transferred,copied,popped,pushedTrue,variableState,
      StackRoutines.transferStacks,StackRoutines.copyStacks]
  have hg15 : g.stacks 15 = unary t.occurrence := by
    simp [g,f,e,c,b,a,transferred,copied,popped,pushedTrue,StackRoutines.transferStacks,
      StackRoutines.copyStacks,variableState]
  have hg19 : g.stacks 19 = [] := by
    simp [g,f,e,c,b,a,transferred,copied,popped,pushedTrue,StackRoutines.transferStacks,
      StackRoutines.copyStacks,variableState]
  obtain ⟨rf,hmax⟩ := maximum_eval g (max 1 d) t.occurrence hg18 hg15 hg19
  have hfinal : (⟨rf,Function.update (Function.update g.stacks 18 []) 15
      (unary (max (max 1 d) t.occurrence))⟩ : Data) =
      variableState rf scopes v mask master (t.add d) := by
    apply congrArg (StructuredProgram.State.mk rf)
    funext i; fin_cases i <;>
      simp [g,f,e,c,b,a,transferred,copied,popped,pushedTrue,StackRoutines.transferStacks,
        StackRoutines.copyStacks,variableState,Totals.add,unary,List.replicate_succ,
        List.reverse_replicate,Nat.add_comm]
  rw [hfinal] at hmax
  have h := (pushTrue_eval 14 a).seq ((pop_eval 3 b).seq
    (hen.seq (hcopy.seq (htransfer.seq hmax))))
  refine ⟨_,rf,?_,h⟩
  have he3 : (e.stacks 3).length = max 1 d := by simp [e]
  have hf3 : (f.stacks 3).length = max 1 d := by
    simp [f,e,copied,StackRoutines.copyStacks]
  rw [he3,hf3]
  omega

def variableStep : Code := .seq countDegree (.seq (pop 13)
  (.seq (.ite 0 (WorkspaceCleanupProgram.command 0 1 [3]) accumulateLow)
    (.seq (pushTrue 2) (peek 13))))

def stepBudget (scopes : List (List ℕ)) (v : ℕ) :=
  SubexpIncidenceSlotProgram.budget scopes scopes.length v + 50*(degree scopes v+1)+50

theorem variableStep_eval (r : Fin 10 → Bool) (scopes : List (List ℕ))
    (v : ℕ) (high : Bool) (mask master : List Bool) (t : Totals) :
    ∃ n rf, n ≤ stepBudget scopes v ∧ Eval variableStep n
      (variableState r scopes v (high::mask) master t)
      (peeked 13 (variableState rf scopes (v+1) mask master
        (if high then t else t.add (degree scopes v)))) := by
  obtain ⟨nc,rc,hnc,hc⟩ := countDegree_eval r scopes v (high::mask) master t
  let a : Data := ⟨rc,Function.update (variableState r scopes v (high::mask) master t).stacks 3
    (unary (degree scopes v+1))⟩
  let b := popped 13 a
  let rt := if high then t else t.add (degree scopes v)
  have hb : b = (⟨b.regs,Function.update (variableState b.regs scopes v mask master t).stacks 3
      (unary (degree scopes v+1))⟩ : Data) := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    funext i; fin_cases i <;> simp [b,a,popped,variableState]
  have hbranch : ∃ nb rb, nb ≤ 40*(degree scopes v+1)+40 ∧
      Eval (.ite 0 (WorkspaceCleanupProgram.command 0 1 [3]) accumulateLow) nb b
        (variableState rb scopes v mask master rt) := by
    cases high with
    | false =>
      obtain ⟨nl,rl,hnl,hl⟩ := accumulateLow_eval b.regs scopes v (degree scopes v) mask master t
      rw [←hb] at hl
      exact ⟨nl+1,rl,by omega,Eval.ite_false (by simp [b,a,popped,readRegs,variableState]) hl⟩
    | true =>
      let e := WorkspaceCleanupProgram.finish (0 : Fin 10) 1 ([3] : List (Fin 21)) b
      have hclean := WorkspaceCleanupProgram.command_eval (0 : Fin 10) 1
        ([3] : List (Fin 21)) (by decide) b
      have heq : e = variableState e.regs scopes v mask master rt := by
        apply congrArg (StructuredProgram.State.mk e.regs)
        funext i; fin_cases i <;> simp [b,a,popped,variableState,rt,BankRoutines.clearBankStacks]
      have hbound : WorkspaceCleanupProgram.cost ([3] : List (Fin 21)) b =
          2*(degree scopes v+1)+3 := by
        simp [WorkspaceCleanupProgram.cost,b,a,popped]
      refine ⟨WorkspaceCleanupProgram.cost ([3] : List (Fin 21)) b + 1,e.regs,?_,?_⟩
      · rw [hbound]; omega
      · have h := Eval.ite_true (no := accumulateLow) (show b.regs 0 = true by simp [b,a,popped,readRegs,variableState]) hclean
        change Eval _ _ b e at h
        rw [heq] at h
        exact h
  obtain ⟨nb,rb,hnb,hbRun⟩ := hbranch
  let c := variableState rb scopes v mask master rt
  let e := pushedTrue 2 c
  have heq : e = variableState e.regs scopes (v+1) mask master rt := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i; fin_cases i <;> simp [c,variableState,unary,List.replicate_succ]
  have hlast := (pushTrue_eval 2 c).seq (peek_eval 13 e)
  rw [heq] at hlast
  refine ⟨_,e.regs,?_,hc.seq ((pop_eval 13 a).seq (hbRun.seq hlast))⟩
  dsimp [stepBudget]
  omega

def variableBudget (scopes : List (List ℕ)) : ℕ → List Bool → ℕ
  | _,[] => 1
  | v,_::bs => stepBudget scopes v + variableBudget scopes (v+1) bs + 1

def variableLoop : Code := .while 1 variableStep
def variableScan : Code := .seq (peek 13) variableLoop

theorem variableLoop_eval (r : Fin 10 → Bool) (scopes : List (List ℕ))
    (v : ℕ) (mask master : List Bool) (t : Totals) :
    ∃ n rf, n ≤ variableBudget scopes v mask ∧ Eval variableLoop n
      (peeked 13 (variableState r scopes v mask master t))
      (variableState rf scopes (v+mask.length) [] master (variableTotals scopes v mask t)) := by
  induction mask generalizing r v t with
  | nil =>
    exact ⟨1,(peeked 13 (variableState r scopes v [] master t)).regs,by rfl,
      Eval.while_false (by simp [peeked,variableState,readRegs])⟩
  | cons b bs ih =>
    let rp := (peeked 13 (variableState r scopes v (b::bs) master t)).regs
    obtain ⟨ni,ri,hni,hi⟩ := variableStep_eval rp scopes v b bs master t
    obtain ⟨nt,rf,hnt,ht⟩ := ih ri (v+1) (if b then t else t.add (degree scopes v))
    refine ⟨ni+nt+1,rf,by dsimp [variableBudget]; omega,?_⟩
    have h := Eval.while_true (show
      (peeked 13 (variableState r scopes v (b::bs) master t)).regs 1 = true by
        simp [peeked,variableState,readRegs]) hi ht
    simpa only [variableLoop, variableTotals, List.length_cons, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h

theorem variableScan_eval (r : Fin 10 → Bool) (scopes : List (List ℕ))
    (v : ℕ) (mask master : List Bool) (t : Totals) :
    ∃ n rf, n ≤ variableBudget scopes v mask+1 ∧ Eval variableScan n
      (variableState r scopes v mask master t)
      (variableState rf scopes (v+mask.length) [] master (variableTotals scopes v mask t)) := by
  obtain ⟨n,rf,hn,he⟩ := variableLoop_eval r scopes v mask master t
  exact ⟨1+n,rf,by omega,(peek_eval 13 (variableState r scopes v mask master t)).seq he⟩

def variableProgram := compiled variableScan 13 16

theorem variableProgram_runsIn (r : Fin 10 → Bool) (scopes : List (List ℕ))
    (v : ℕ) (mask master : List Bool) (t : Totals) :
    ∃ rf, RunsIn variableProgram (variableBudget scopes v mask+2)
      ((variableState r scopes v mask master t).withPC (some variableProgram.entry))
      ((variableState rf scopes (v+mask.length) [] master (variableTotals scopes v mask t)).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := variableScan_eval r scopes v mask master t
  exact ⟨rf,n+1,by omega,compiled_halt_trace he 13 16⟩

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
