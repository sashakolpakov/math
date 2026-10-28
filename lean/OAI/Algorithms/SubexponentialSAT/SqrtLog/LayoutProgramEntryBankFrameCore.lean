import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramStaging
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisEntryCore
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Frame and measured-call lemmas used by the concrete entry-bank program.
The state maps below only specify the outcomes of actual fixed commands. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem compare_lifted {S : ℕ} (ports : Fin 32 → Fin S)
    (hp : Function.Injective ports) (a : State 16 S)
    (h17 : a.stacks (ports 17)=[]) (h28 : a.stacks (ports 28)=[])
    (h27 : a.stacks (ports 27)=[]) (h31 : a.stacks (ports 31)=[]) :
    ∃ n ≤ 18*(a.stacks (ports 0)).length+9*(a.stacks (ports 1)).length+32,
      ∃ e : State 16 S,
      Eval (liftCommand (GlobalBasisEntryCore.compare 0 1) 0 1 id ports) n a e ∧
      e.stacks=a.stacks ∧ e.regs 6=a.regs 6 ∧
      e.regs 7=decide (a.stacks (ports 0)=a.stacks (ports 1)) := by
  let p := projectState id ports a
  obtain ⟨n,b,hn,he,hbs,h6,h7⟩ := GlobalBasisEntryCore.compare_eval 0 1
    (by decide) (by decide) p h17 h28 h27 h31
  let e := embedState id ports a b
  refine ⟨n+1,by simpa [p,projectState] using Nat.add_le_add_right hn 1,e,
    eval_liftCommand_from_state _ 0 1 id ports a Function.injective_id hp he,?_,?_,?_⟩
  · change Function.extend ports b.stacks a.stacks=a.stacks
    rw [hbs]
    exact congrArg StructuredProgram.State.stacks
      (embedState_project id ports a Function.injective_id hp)
  · exact (embedState_register id ports a b Function.injective_id 6).trans h6
  · exact (embedState_register id ports a b Function.injective_id 7).trans h7

theorem staging_result_temp {r s : ℕ} (v pr : Fin r) (tmp : Fin s)
    (ops : List (Staging.Action s)) (a : State r s)
    (hv : ∀ op∈ops,op.Valid tmp) (ht : a.stacks tmp=[]) :
    (Staging.result v pr ops a).stacks tmp=[] := by
  induction ops generalizing a with
  | nil => exact ht
  | cons op ops ih =>
    exact ih (Staging.actionResult v pr op a)
      (fun x hx => hv x (by simp [hx]))
      (Staging.action_temp v pr tmp op a (hv op (by simp)) ht)

theorem staging_register_frame {r s : ℕ} (v pr j : Fin r)
    (hjv : j≠v) (hjp : j≠pr) (ops : List (Staging.Action s)) (a : State r s) :
    (Staging.result v pr ops a).regs j=a.regs j := by
  induction ops generalizing a with
  | nil => rfl
  | cons op ops ih =>
    rw [Staging.result,ih]
    cases op <;> simp [Staging.actionResult,readRegs,TupleProgram.pushedState,hjv,hjp]

/-- Every clear is charged, even when a repeated port is already empty. -/
theorem clear_cost_le {r s : ℕ} (v pr : Fin r) (ports : List (Fin s))
    (a : State r s) :
    Staging.cost v pr (ports.map Staging.Action.clear) a ≤
      2*(ports.map (fun j => (a.stacks j).length)).sum+3*ports.length := by
  induction ports generalizing a with
  | nil => simp [Staging.cost]
  | cons j js ih =>
    let b := Staging.actionResult v pr (.clear j) a
    have hb : ∀ i, (b.stacks i).length ≤ (a.stacks i).length := by
      intro i
      simp only [b,Staging.clear_action_result]
      split_ifs <;> simp
    have hsum' : (js.map (fun i => (b.stacks i).length)).sum ≤
        (js.map (fun i => (a.stacks i).length)).sum := by
      clear ih
      induction js with
      | nil => simp
      | cons i is hi => simpa using Nat.add_le_add (hb i) hi
    have h := ih b
    dsimp only [b] at h hsum'
    simp only [List.map_cons,Staging.cost,Staging.actionCost,List.sum_cons,List.length_cons]
    omega

theorem sum_map_le_length {α : Type*} (xs : List α) (f : α → ℕ) (B : ℕ)
    (h : ∀ x∈xs,f x ≤ B) : (xs.map f).sum ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    calc
      f x+(xs.map f).sum ≤ B+xs.length*B := Nat.add_le_add hx hs
      _ = (xs.length+1)*B := by ring

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame

end OAI.Algorithms
