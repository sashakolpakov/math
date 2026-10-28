import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! A finite sequence of genuine copy, clear and constant-bit instructions.
The functional result is only a trace specification; execution uses the
fixed primitive instruction tables. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Staging

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

variable {r s : ℕ}

inductive Action (s : ℕ) where
  | copy (src dst : Fin s)
  | clear (dst : Fin s)
  | push (dst : Fin s) (bit : Bool)
  deriving DecidableEq

def Action.Valid (tmp : Fin s) : Action s → Prop
  | .copy src dst => src≠dst ∧ src≠tmp ∧ tmp≠dst
  | .clear _ => True
  | .push dst _ => tmp≠dst

instance (tmp : Fin s) (a : Action s) : Decidable (a.Valid tmp) := by
  cases a <;> unfold Action.Valid <;> infer_instance

def action (v pr : Fin r) (tmp : Fin s) : Action s → Cmd r s
  | .copy src dst => .call (StackRoutines.copyProgram src dst tmp v pr)
  | .clear dst => .call (StackRoutines.clearProgram dst v pr)
  | .push dst b => TupleProgram.pushConst dst v b

def actionResult (v pr : Fin r) : Action s → State r s → State r s
  | .copy src dst,a => ⟨readRegs a.regs v pr none,StackRoutines.copyStacks src dst a.stacks⟩
  | .clear dst,a => ⟨readRegs a.regs v pr none,StackRoutines.clearStacks dst a.stacks⟩
  | .push dst b,a => TupleProgram.pushedState dst v b a

def actionCost : Action s → State r s → ℕ
  | .copy src _,a => 7*(a.stacks src).length+5
  | .clear dst,a => 2*(a.stacks dst).length+3
  | .push _ _,_ => 2

theorem action_eval (v pr : Fin r) (tmp : Fin s) (hvp : v≠pr)
    (op : Action s) (a : State r s) (hv : op.Valid tmp) (ht : a.stacks tmp=[]) :
    Eval (action v pr tmp op) (actionCost op a) a (actionResult v pr op a) := by
  cases op with
  | copy src dst => exact TupleProgram.copy_eval src dst tmp v pr hv.1 hv.2.1 hv.2.2 hvp a ht
  | clear dst => exact TupleProgram.clear_eval dst v pr a
  | push dst b => exact TupleProgram.pushConst_eval dst v b a

theorem action_temp (v pr : Fin r) (tmp : Fin s)
    (op : Action s) (a : State r s) (hv : op.Valid tmp) (ht : a.stacks tmp=[]) :
    (actionResult v pr op a).stacks tmp=[] := by
  cases op with
  | copy src dst => simp [actionResult,StackRoutines.copyStacks,hv.2.2,ht]
  | clear dst => by_cases h : tmp=dst <;> simp [actionResult,StackRoutines.clearStacks,h,ht]
  | push dst b => simp only [Action.Valid] at hv; simp [actionResult,TupleProgram.pushedState,hv,ht]

def sequence (v pr : Fin r) (tmp : Fin s) : List (Action s) → Cmd r s
  | [] => .base .skip
  | op::ops => .seq (action v pr tmp op) (sequence v pr tmp ops)

def result (v pr : Fin r) : List (Action s) → State r s → State r s
  | [],a => a
  | op::ops,a => result v pr ops (actionResult v pr op a)

def cost (v pr : Fin r) : List (Action s) → State r s → ℕ
  | [],_ => 0
  | op::ops,a => actionCost op a+cost v pr ops (actionResult v pr op a)

theorem sequence_eval (v pr : Fin r) (tmp : Fin s) (hvp : v≠pr)
    (ops : List (Action s)) (a : State r s)
    (hv : ∀ op∈ops,op.Valid tmp) (ht : a.stacks tmp=[]) :
    Eval (sequence v pr tmp ops) (cost v pr ops a) a (result v pr ops a) := by
  induction ops generalizing a with
  | nil => exact .base (.skip _)
  | cons op ops ih =>
    have hop := hv op (by simp)
    exact (action_eval v pr tmp hvp op a hop ht).seq
      (ih (actionResult v pr op a) (fun x hx=>hv x (by simp [hx]))
        (action_temp v pr tmp op a hop ht))

def Action.destination : Action s → Fin s
  | .copy _ dst => dst
  | .clear dst => dst
  | .push dst _ => dst

theorem action_frame (v pr : Fin r) (op : Action s) (a : State r s)
    (j : Fin s) (hj : j≠op.destination) :
    (actionResult v pr op a).stacks j=a.stacks j := by
  cases op <;> simp_all [Action.destination,actionResult,StackRoutines.copyStacks,
    StackRoutines.clearStacks,TupleProgram.pushedState]

theorem result_frame (v pr : Fin r) (ops : List (Action s)) (a : State r s)
    (j : Fin s) (hj : ∀ op∈ops,j≠op.destination) :
    (result v pr ops a).stacks j=a.stacks j := by
  induction ops generalizing a with
  | nil => rfl
  | cons op ops ih =>
    exact (ih (actionResult v pr op a) (fun x hx=>hj x (by simp [hx]))).trans
      (action_frame v pr op a j (hj op (by simp)))

theorem clear_action_result (v pr : Fin r) (a : State r s) (i j : Fin s) :
    (actionResult v pr (.clear i) a).stacks j=if j=i then [] else a.stacks j := by
  simp [actionResult,StackRoutines.clearStacks,Function.update_apply]

theorem result_clears (v pr : Fin r) (ports : List (Fin s)) (a : State r s) (j : Fin s) :
    (result v pr (ports.map Action.clear) a).stacks j=if j∈ports then [] else a.stacks j := by
  induction ports generalizing a with
  | nil => simp [result]
  | cons p ps ih =>
    simp only [List.map_cons,result,ih,clear_action_result,List.mem_cons]
    by_cases hp : j=p <;> by_cases hs : j∈ps <;> simp [hp,hs]

end SubexponentialSAT.SqrtLog.LayoutProgram.Staging

end OAI.Algorithms
