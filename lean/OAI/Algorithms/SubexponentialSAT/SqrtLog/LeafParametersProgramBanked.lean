import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramNative

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard


open BitProgram StructuredCalls StructuredProgram

theorem command_clears (a : Data) :
    ∃ b, Eval command (1+checksCost allChecks a) a b ∧ ∀ i, b.stacks i=[] := by
  let a0 := (Atom.set (8 : Fin 9) true).eval a
  obtain ⟨b,he,hacc,hframe,hclear⟩ := checks_eval allChecks (List.nodup_finRange 10) a0
  refine ⟨b,(Eval.base (.atom _ _)).seq he,?_⟩
  intro i
  let j : Fin 10 := ⟨i.val/2,by omega⟩
  let bit : Fin 2 := ⟨i.val%2,Nat.mod_lt _ (by decide)⟩
  have hi : pair j bit=i := by
    apply Fin.ext
    dsimp [pair,j,bit]
    omega
  rw [← hi]
  exact hclear j (by simp [allChecks]) bit

end SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

def guardedWords (w : Words) : Words := fun a => if a.val < 44 then w a else []

def guardedModel (x : Input) (l : Fin 8 → ℕ) : Model :=
  { val := fun a => if a.val < 44 then (Prepared.finalModel x l).val a else 0
    len := fun a => if a.val < 44 then (Prepared.finalModel x l).len a else 0 }

theorem guardedModel_public (x : Input) (l : Fin 8 → ℕ) (i : Fin 12) :
    (guardedModel x l).val (publicSlot i)=(Layout.model x l).val (publicSlot i) := by
  change (if (publicSlot i).val < 44 then (Prepared.finalModel x l).val (publicSlot i) else 0)=_
  rw [ite_eq_left (publicSlot_lt i)]
  exact guard_preserves_public (Layout.model x l) i

private theorem guard_code_preserves_input (i : Fin 8) :
    ∀ j ∈ GuardSetup.code, Circuit.output j ≠ i.castAdd 56 := by
  fin_cases i <;> decide

theorem guardedModel_input (x : Input) (l : Fin 8 → ℕ) (i : Fin 8) :
    (guardedModel x l).val (i.castAdd 56)=Layout.initialValues x (i.castAdd 56) := by
  have hi : (i.castAdd 56).val < 44 := by have := i.isLt; simpa using (show i.val < 44 by omega)
  change (if (i.castAdd 56).val < 44 then (Prepared.finalModel x l).val (i.castAdd 56) else 0)=_
  rw [ite_eq_left hi]
  calc
    _ = (Layout.model x l).val (i.castAdd 56) := by
      exact result_value_frame GuardSetup.code (Layout.model x l) _
        (guard_code_preserves_input i)
    _ = _ := Layout.model_inputs x l i

theorem guardedModel_precision (x : Input) (l : Fin 8 → ℕ) (hm : x.clauses≠0) :
    (guardedModel x l).val 33=(produce x).t :=
  (guardedModel_public x l 8).trans (Layout.model_precision x l hm)

theorem guardedModel_degree (x : Input) (l : Fin 8 → ℕ) (hq : (produce x).Q≠0) :
    (guardedModel x l).val 34=(produce x).d :=
  (guardedModel_public x l 9).trans (Layout.model_degree x l hq)

theorem guardedModel_radius (x : Input) (l : Fin 8 → ℕ) :
    (guardedModel x l).val 18=(produce x).r :=
  (guardedModel_public x l 3).trans (Layout.model_core_values x l).2.2.2.1

private theorem guard_frame (r : Fin 9 → Bool) (w : Words) (b : BitGuard.Data)
    (hb : ∀ i, b.stacks i=[]) :
    embedState id guardStacks (state r w) b=state b.regs (guardedWords w) := by
  apply embedState_eq_of_ports id guardStacks (state r w) _ b
    Function.injective_id guardStacks_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i
    rw [hb]
    simp [state,Bank.state,guardedWords,guardStacks]
  · intro i hi
    by_cases hlo : i.val < 44
    · simp [state,Bank.state,guardedWords,show i.val < 64 by omega,hlo]
    · have hhigh : 64 ≤ i.val := by
        by_contra hn
        have hlt : i.val < 64 := by omega
        let j : Fin 20 := ⟨i.val-44,by omega⟩
        apply hi
        refine ⟨j,?_⟩
        apply Fin.ext
        dsimp [guardStacks,j]
        omega
      simp [state,Bank.state,show ¬i.val < 64 by omega]

private theorem banked_trace (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Layout.initialModel x l) w) :
    ∃ t rf wf, Eval setup t (state r w) (state rf wf) ∧
      Shape (guardedModel x l) wf := by
  obtain ⟨t,rf,w',he,hs',ht⟩ := numeric_eval x l w r hs
  let mid := state rf w'
  obtain ⟨b,hb,hclear⟩ := BitGuard.command_clears (projectState id guardStacks mid)
  have hc := eval_liftCommand_from_state BitGuard.command 0 0 id guardStacks mid
    Function.injective_id guardStacks_injective hb
  rw [guard_frame rf w' b hclear] at hc
  refine ⟨t+((1+BitGuard.checksCost BitGuard.allChecks (projectState id guardStacks mid))+1),
    b.regs,guardedWords w',he.seq hc,?_⟩
  constructor
  · intro a
    by_cases ha : a.val < 44
    · simpa [guardedModel,guardedWords,ha] using hs'.1 a
    · simp [guardedModel,guardedWords,ha]
  · intro a
    by_cases ha : a.val < 44
    · simpa [guardedModel,guardedWords,ha] using hs'.2 a
    · simp [guardedModel,guardedWords,ha]

/-- The actual post-guard endpoint has an empty physical work bank. Its low
table keeps all input and parameter words and clears the comparison operands.
The separate ninth register retains the guard result. -/
theorem setup_banked_output (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Layout.initialModel x l) w) :
    ∃ t rf wf, Eval setup t (state r w) (state rf wf) ∧
      (rf 8=true ↔ Guard x) ∧ Shape (guardedModel x l) wf ∧
      (Guard x → Layout.EncodesParameters (produce x) wf) ∧ t ≤ runtimeBound x l := by
  obtain ⟨u,rf,wf,he,hshape⟩ := banked_trace x l w r hs
  obtain ⟨t,final,ht,hguard,hparameters,hbound⟩ := setup_output x l w r hs
  have hf := ht.final_unique (Bank.port 0) he
  subst final
  refine ⟨t,rf,wf,ht,hguard,hshape,?_,hbound⟩
  simpa only [state_port] using hparameters

theorem banked_projection (r : Fin 9 → Bool) (w : Words) :
    projectState registers id (state r w)=Bank.state (r ∘ registers) w := rfl

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

end OAI.Algorithms
