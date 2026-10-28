import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramCompare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramCNF
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! Paid factor classification and source lookup. IDs are runtime data. -/
namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 8 16
abbrev Code := Cmd 8 16
abbrev unary (n : ℕ) := List.replicate n true

def copy (src dst : Fin 16) : Code := .call (StackRoutines.copyProgram src dst 14 0 1)
def clear (src : Fin 16) : Code := .call (StackRoutines.clearProgram src 0 1)
def cleared (d : Data) (src : Fin 16) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem clear_eval (d : Data) (src : Fin 16) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared d src) := by
  have h := StackRoutines.clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks
  have ht := StackRoutines.halt_after_trace _ h 2 rfl rfl
  apply Eval.call
  simpa [clear,cleared,StackRoutines.clearProgram,StackRoutines.clearResult,
    StackRoutines.clearStacks,StructuredProgram.State.withPC,Nat.add_assoc] using ht

def Stable (d e : Data) : Prop := ∀ i : Fin 8, 4 ≤ i.val → e.regs i = d.regs i

theorem stable_refl (d : Data) : Stable d d := fun _ _ => rfl

theorem stable_trans {d e f : Data} (h : Stable d e) (h' : Stable e f) : Stable d f :=
  fun i hi => (h' i hi).trans (h i hi)

/-- The existing comparison only removes cells; this records its paid cleanup bound. -/
theorem less_trace (left right : List Bool) (regs : Fin 4 → Bool) :
    ∃ n rf l r, n ≤ 4*left.length+6 ∧
      Trace CodeSearchProgram.unaryLessProgram n
        (CodeSearchProgram.unaryLessCfg (some 0) regs left right)
        (CodeSearchProgram.unaryLessCfg none rf l r) ∧
      rf 3=decide (left.length < right.length) ∧ l.length ≤ left.length ∧ r.length ≤ right.length := by
  induction left generalizing right regs with
  | nil =>
    refine ⟨5,_,[],right,by simp,CodeSearchProgram.unaryLess_nil regs right,?_,by simp,le_rfl⟩
    cases right <;> simp
  | cons a left ih =>
    cases right with
    | nil =>
      refine ⟨6,_,left,[],by simp,CodeSearchProgram.unaryLess_right_nil regs a left,by simp,by simp,le_rfl⟩
    | cons b right =>
      obtain ⟨n,rf,l,r,hn,ht,hf,hl,hr⟩ :=
        ih right (readRegs (readRegs regs 0 1 (some a)) 0 2 (some b))
      refine ⟨4+n,rf,l,r,?_,(CodeSearchProgram.unaryLess_round regs a b left right).trans ht,?_,?_,?_⟩
      · simp only [List.length_cons]; omega
      · simpa using hf
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega

def cmpRegs : Fin 4 → Fin 8 := Fin.castAdd 4
def cmpPorts : Fin 2 → Fin 16 := ![8,9]
def compare : Code := .call (ProgramLinking.liftProgram CodeSearchProgram.unaryLessProgram cmpRegs cmpPorts)
def lessClean : Code := .seq compare (.seq (clear 8) (clear 9))

theorem lessClean_eval (d : Data) :
    ∃ n e, n ≤ 6*(d.stacks 8).length+2*(d.stacks 9).length+12 ∧
      Eval lessClean n d e ∧ e.regs 3=decide ((d.stacks 8).length < (d.stacks 9).length) ∧
      e.stacks=Function.update (Function.update d.stacks 8 []) 9 [] ∧ Stable d e := by
  obtain ⟨n,rf,l,r,hn,ht,hf,hl,hr⟩ := less_trace (d.stacks 8) (d.stacks 9) (d.regs ∘ cmpRegs)
  have hir : Function.Injective cmpRegs := Fin.castAdd_injective _ _
  have hip : Function.Injective cmpPorts := by decide
  let a : State 4 2 := ⟨d.regs ∘ cmpRegs,![d.stacks 8,d.stacks 9]⟩
  let b : State 4 2 := ⟨rf,![l,r]⟩
  let c := embedState cmpRegs cmpPorts d b
  have ha : embedState cmpRegs cmpPorts d a=d := by
    apply embedState_eq_of_ports _ _ _ _ _ hir hip
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have he := eval_call_lifted CodeSearchProgram.unaryLessProgram cmpRegs cmpPorts d hir hip
    (a := a) (b := b) ht
  rw [ha] at he
  have hc8 : c.stacks 8=l := embedState_stack _ _ _ _ hip 0
  have hc9 : c.stacks 9=r := embedState_stack _ _ _ _ hip 1
  have hc3 : c.regs 3=rf 3 := embedState_register _ _ _ _ hir 3
  let e := cleared (cleared c 8) 9
  have heval := he.seq ((clear_eval c 8).seq (clear_eval (cleared c 8) 9))
  refine ⟨n+(2*l.length+3+(2*r.length+3)),e,by omega,?_,?_,?_,?_⟩
  · simpa [e, lessClean, compare, hc8, hc9, cleared] using heval
  · simpa [e,cleared,readRegs,hc3] using hf
  · funext i
    by_cases h8 : i=8
    · subst i; simp [e,cleared]
    by_cases h9 : i=9
    · subst i; simp [e,cleared]
    · have hframe : c.stacks i=d.stacks i := by
        apply embedState_stack_frame
        rintro ⟨j,hj⟩
        fin_cases j <;> simp_all [cmpPorts]
      simpa [e,cleared,h8,h9] using hframe
  · intro i hi
    have hi0 : i≠0 := by intro h; subst i; simp at hi
    have hi1 : i≠1 := by intro h; subst i; simp at hi
    have hframe : c.regs i=d.regs i := by
      apply embedState_register_frame
      rintro ⟨j,hj⟩
      have hh := congrArg Fin.val hj
      simp [cmpRegs] at hh
      omega
    simpa [e,cleared,readRegs,hi0,hi1] using hframe

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
