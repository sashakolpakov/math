import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! The node index and palette size are runtime inputs. This fixed program
initializes the head countdown and computes the first physical color address
by real unary multiplication. Subsequent heads increment that address. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Address
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BasisTransposePlanProgram

def command : Code := .seq (copy 2 5) (.seq multiply (copy 0 3))
def program := compiled command 2 4
def input (regs : Fin 3 → Bool) (r t : ℕ) : Data :=
  ⟨regs,![unary r,[],unary t,[],[],[],[]]⟩
def result (regs : Fin 3 → Bool) (r t : ℕ) : Data :=
  ⟨regs,![unary r,[],unary t,unary r,unary (t*r),[],[]]⟩
def budget (r t : ℕ) := t*(7*r+14)+7*r+13

theorem command_eval (regs : Fin 3 → Bool) (r t : ℕ) :
    ∃ n ≤ budget r t-1, ∃ rf, Eval command n (input regs r t) (result rf r t) := by
  let a := input regs r t
  let b := copied 2 5 a
  have h1 := copy_eval 2 5 a (by decide) (by decide) (by decide) rfl
  obtain ⟨n,c,h2,hn,hs⟩ := multiply_eval r t b
    (by simp [b,a,input])
    (by simp [b,a,input])
    (by simp [b,a,input])
  have hc0 : c.stacks 0=unary r := by simp [hs,b,a,input]
  have hc6 : c.stacks 6=[] := by simp [hs,b,a,input]
  let e := copied 0 3 c
  have h3 := copy_eval 0 3 c (by decide) (by decide) (by decide) hc6
  have he : e=result e.regs r t := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    fin_cases i <;> simp [hs,b,a,input,StackRoutines.copyStacks]
  change Eval _ _ c e at h3
  rw [he] at h3
  refine ⟨_,?_,e.regs,h1.seq (h2.seq h3)⟩
  simp [a,input,unary,hc0]
  have hb : budget r t-1=t*(7*r+14)+7*r+12 := by unfold budget; omega
  rw [hb]
  nlinarith

theorem program_runsIn (regs : Fin 3 → Bool) (r t : ℕ) :
    ∃ rf, RunsIn program (budget r t) ((input regs r t).withPC (some program.entry))
      ((result rf r t).withPC none) := by
  obtain ⟨n,hn,rf,he⟩ := command_eval regs r t
  exact ⟨rf,n+1,by unfold budget at *; omega,compiled_halt_trace he 2 4⟩

theorem budget_polynomial (r t : ℕ) : budget r t ≤ 40*(r+t+1)^2 := by
  unfold budget
  nlinarith [Nat.zero_le ((r-t)^2)]

def increment : Code := SubexponentialSAT.Subexp.TupleProgram.pushConst 4 0 true

theorem increment_eval (d : Data) (z : ℕ) (hz : d.stacks 4=unary z) :
    Eval increment 2 d
      ⟨Function.update d.regs 0 true,Function.update d.stacks 4 (unary (z+1))⟩ := by
  have h := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (4 : Fin 7) (0 : Fin 3) true d
  simpa [increment,SubexponentialSAT.Subexp.TupleProgram.pushedState,hz,unary,List.replicate_succ] using h

theorem program_primitive (regs : Fin 3 → Bool) (r t : ℕ) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program*budget r t)
      (primitiveCfg program ((input regs r t).withPC (some program.entry)))
      (primitiveCfg program ((result rf r t).withPC none)) := by
  obtain ⟨rf,he⟩ := program_runsIn regs r t
  exact ⟨rf,primitive_execution program he⟩

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Address

end OAI.Algorithms
