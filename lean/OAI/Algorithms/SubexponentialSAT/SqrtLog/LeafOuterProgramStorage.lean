import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BankRoutines
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramCleanupWide
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Static routing for the outer leaf. Each route clears its destination and
then calls the measured physical copy routine. The route list belongs to the
fixed program, while every copied bit and every cleanup bit is charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

abbrev Data := State 40 896
abbrev Route := Fin 896 × Fin 896

def routeValid (p : Route) : Prop :=
  p.1 ≠ p.2 ∧ p.1 ≠ 767 ∧ p.2 ≠ 767

abbrev route (p : Route) : Cmd 40 896 :=
  .seq (.call (clearProgram p.2 0 1)) (.call (copyProgram p.1 p.2 767 0 1))

def routed (p : Route) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,Function.update a.stacks p.2 (a.stacks p.1)⟩

def routeCost (p : Route) (a : Data) : ℕ :=
  2*(a.stacks p.2).length+7*(a.stacks p.1).length+8

theorem route_eval (p : Route) (hp : routeValid p) (a : Data)
    (ht : a.stacks 767 = []) : Eval (route p) (routeCost p a) a (routed p a) := by
  obtain ⟨hsd,hst,hdt⟩ := hp
  have hc := BankRoutines.clear_call_eval p.2 (0 : Fin 40) 1 a.regs a.stacks
  have hsrc : clearStacks p.2 a.stacks p.1 = a.stacks p.1 :=
    clearStacks_frame _ _ _ hsd
  have htmp : clearStacks p.2 a.stacks 767 = [] := by
    rw [clearStacks_frame _ _ _ (Ne.symm hdt),ht]
  have hf := BankRoutines.copy_call_eval p.1 p.2 (767 : Fin 896) (0 : Fin 40) 1
    hsd hst (Ne.symm hdt) (by decide) (readRegs a.regs 0 1 none)
    (clearStacks p.2 a.stacks) htmp
  have he : copyStacks p.1 p.2 (clearStacks p.2 a.stacks) =
      Function.update a.stacks p.2 (a.stacks p.1) := by
    funext i
    by_cases hi : i = p.2
    · subst i; simp [copyStacks,clearStacks,hsd]
    · simp [copyStacks,clearStacks,hi]
  have hcost : 2*(a.stacks p.2).length+3+(7*(a.stacks p.1).length+5) = routeCost p a := by
    unfold routeCost
    omega
  simpa only [route,routed,hsrc,he,readRegs_reset,hcost] using hc.seq hf

def routes : List Route → Cmd 40 896
  | [] => .call (clearProgram 767 0 1)
  | p::ps => .seq (route p) (routes ps)

def routesState : List Route → Data → Data
  | [],a => ⟨readRegs a.regs 0 1 none,a.stacks⟩
  | p::ps,a => routesState ps (routed p a)

def routesCost : List Route → Data → ℕ
  | [],_ => 3
  | p::ps,a => routeCost p a+routesCost ps (routed p a)

theorem routes_eval (ps : List Route) (hp : ∀ p ∈ ps, routeValid p)
    (a : Data) (ht : a.stacks 767 = []) :
    Eval (routes ps) (routesCost ps a) a (routesState ps a) := by
  induction ps generalizing a with
  | nil =>
    have h := BankRoutines.clear_call_eval (767 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
    simpa only [routes,routesCost,routesState,ht,List.length_nil,Nat.mul_zero,
      Nat.zero_add,BankRoutines.clearStacks_eq_self_of_empty _ _ ht] using h
  | cons p ps ih =>
    have h := hp p (by simp)
    have htmp : (routed p a).stacks 767 = [] := by
      simpa only [routed,Function.update_of_ne (Ne.symm h.2.2)] using ht
    exact (route_eval p h a ht).seq (ih (fun q hq => hp q (by simp [hq])) (routed p a) htmp)

theorem routes_frame (ps : List Route) (a : Data) (i : Fin 896)
    (hi : ∀ p ∈ ps, p.2 ≠ i) : (routesState ps a).stacks i = a.stacks i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [routesState,ih (routed p a) (fun q hq => hi q (by simp [hq]))]
    exact Function.update_of_ne (Ne.symm (hi p (by simp))) _ _

theorem routes_cost_bound (ps : List Route) (a : Data) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    routesCost ps a ≤ ps.length*(9*B+8)+3 := by
  induction ps generalizing a with
  | nil => simp [routesCost]
  | cons p ps ih =>
    have hb' : ∀ i, ((routed p a).stacks i).length ≤ B := by
      intro i
      by_cases h : i=p.2
      · subst i; simpa [routed] using hb p.1
      · simpa [routed,h] using hb i
    have hh := ih (routed p a) hb'
    have h1 := hb p.1
    have h2 := hb p.2
    simp only [routesCost,routeCost,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def workerStack (i : Fin 768) : Fin 896 := i.castAdd 128
abbrev clearWorker : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram LeafProgram.Cleanup.Wide.program id workerStack)

/-- Static input and output routing around an actual finite subprogram. -/
abbrev stage {r s l : ℕ} (inputs : List Route) (p : Program r s l)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (outputs : List Route) : Cmd 40 896 :=
  .seq (routes inputs) <| .seq (.call (ProgramLinking.liftProgram p register stack)) <|
    .seq (routes outputs) clearWorker

noncomputable def workerCleared (a : Data) : Data :=
  embedState id workerStack a LeafProgram.Cleanup.Wide.blank

theorem clearWorker_eval (a : Data) (ht : a.stacks 767 = []) :
    Eval clearWorker
      (LeafProgram.Cleanup.Wide.budget (projectState id workerStack a)+1)
      a (workerCleared a) := by
  have h := LeafProgram.Cleanup.Wide.lifted id workerStack Function.injective_id
    (Fin.castAdd_injective 768 128) a (projectState id workerStack a) ht
  simpa only [clearWorker,workerCleared,embedState_project id workerStack a
    Function.injective_id (Fin.castAdd_injective 768 128)] using h

theorem clearWorker_stack (a : Data) (i : Fin 768) :
    (workerCleared a).stacks (workerStack i) = [] :=
  embedState_stack id workerStack a LeafProgram.Cleanup.Wide.blank
    (Fin.castAdd_injective 768 128) i

theorem clearWorker_frame (a : Data) (i : Fin 896) (hi : 768 ≤ i.val) :
    (workerCleared a).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  simp only [workerStack,Fin.val_castAdd] at hv
  omega

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
