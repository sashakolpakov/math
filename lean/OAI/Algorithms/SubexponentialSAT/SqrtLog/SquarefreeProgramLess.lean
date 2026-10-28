import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramCompare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramNat

namespace OAI.Algorithms

/-! Fixed unary comparison with explicit residual-length bounds and paid
cleanup. Register 4 is a caller-owned Boolean saved across this operation. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.CodeSearchProgram

theorem unaryLess_trace_bounded (left right : List Bool) (regs : Fin 4 → Bool) :
    ∃ n rf l r, n ≤ 4 * left.length + 6 ∧
      Trace unaryLessProgram n (unaryLessCfg (some 0) regs left right)
        (unaryLessCfg none rf l r) ∧
      rf 3 = decide (left.length < right.length) ∧
      l.length ≤ left.length ∧ r.length ≤ right.length := by
  induction left generalizing right regs with
  | nil =>
      refine ⟨5, _, [], right, by simp, unaryLess_nil regs right, ?_, by simp, le_rfl⟩
      cases right <;> simp
  | cons a left ih =>
      cases right with
      | nil =>
          exact ⟨6, _, left, [], by simp, unaryLess_right_nil regs a left, by simp, by simp, by simp⟩
      | cons b right =>
          obtain ⟨n, rf, l, r, hn, ht, hf, hl, hr⟩ :=
            ih right (readRegs (readRegs regs 0 1 (some a)) 0 2 (some b))
          refine ⟨4 + n, rf, l, r, ?_, (unaryLess_round regs a b left right).trans ht, ?_, by simp; omega, by simp; omega⟩
          · simp only [List.length_cons]
            omega
          · simpa using hf

def lessRegs : Fin 4 → Fin 5 := Fin.castAdd 1

theorem lessRegs_injective : Function.Injective lessRegs := Fin.castAdd_injective _ _

abbrev lessAt {s : ℕ} (src dst : Fin s) : Cmd 5 s :=
  .call (ProgramLinking.liftProgram unaryLessProgram lessRegs (natPorts src dst))

abbrev clearAt {s : ℕ} (src : Fin s) : Cmd 5 s :=
  .call (StackRoutines.clearProgram src (0 : Fin 5) 1)

def clearedAt {s : ℕ} (d : State 5 s) (src : Fin s) : State 5 s :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem clearAt_eval {s : ℕ} (d : State 5 s) (src : Fin s) :
    Eval (clearAt src) (2*(d.stacks src).length+3) d (clearedAt d src) := by
  apply Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 5) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [clearedAt,StackRoutines.clearResult,StackRoutines.clearStacks,
    StructuredProgram.State.withPC,StackRoutines.clearProgram,Nat.add_assoc] using hh

theorem lessAt_eval {s : ℕ} (d : State 5 s) (src dst : Fin s) (hsd : src ≠ dst) :
    ∃ time ≤ 4*(d.stacks src).length+6, ∃ rf l r,
      Eval (lessAt src dst) time d
        (⟨rf,Function.update (Function.update d.stacks src l) dst r⟩ : State 5 s) ∧
      rf 3 = decide ((d.stacks src).length < (d.stacks dst).length) ∧
      rf 4 = d.regs 4 ∧ l.length ≤ (d.stacks src).length ∧ r.length ≤ (d.stacks dst).length := by
  obtain ⟨time,rr,l,r,ht,h,hr,hl,hrlen⟩ :=
    unaryLess_trace_bounded (d.stacks src) (d.stacks dst) (d.regs ∘ lessRegs)
  let a : State 4 2 := ⟨d.regs ∘ lessRegs, ![d.stacks src,d.stacks dst]⟩
  let b : State 4 2 := ⟨rr,![l,r]⟩
  let rf := (embedState lessRegs (natPorts src dst) d b).regs
  have ha : embedState lessRegs (natPorts src dst) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ lessRegs_injective (natPorts_injective src dst hsd)
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hb : embedState lessRegs (natPorts src dst) d b =
      (⟨rf,Function.update (Function.update d.stacks src l) dst r⟩ : State 5 s) := by
    apply embedState_eq_of_ports _ _ _ _ _ lessRegs_injective (natPorts_injective src dst hsd)
    · intro i; exact embedState_register lessRegs (natPorts src dst) d b lessRegs_injective i
    · intro i hi; exact embedState_register_frame lessRegs (natPorts src dst) d b i hi
    · intro i; fin_cases i <;> simp [natPorts,ParserProgram.pair,b,hsd]
    · intro i hi
      have hsrc : i ≠ src := fun he => hi ⟨0, by simpa [natPorts] using he.symm⟩
      have hdst : i ≠ dst := fun he => hi ⟨1, by simpa [natPorts] using he.symm⟩
      simp [hsrc,hdst]
  have htrace : Trace unaryLessProgram time (a.withPC (some unaryLessProgram.entry)) (b.withPC none) := h
  have he := eval_call_lifted unaryLessProgram lessRegs (natPorts src dst) d
    lessRegs_injective (natPorts_injective src dst hsd) htrace
  change Eval (lessAt src dst) time
    (embedState lessRegs (natPorts src dst) d a) (embedState lessRegs (natPorts src dst) d b) at he
  rw [ha,hb] at he
  refine ⟨time,ht,rf,l,r,he,?_,?_,hl,hrlen⟩
  · have hp := embedState_register lessRegs (natPorts src dst) d b lessRegs_injective 3
    simpa [rf,lessRegs,b,hr] using hp
  · apply embedState_register_frame
    rintro ⟨i,hi⟩
    fin_cases i <;> simp [lessRegs] at hi

abbrev lessClear {s : ℕ} (src dst : Fin s) : Cmd 5 s :=
  .seq (lessAt src dst) (.seq (clearAt src) (clearAt dst))

theorem lessClear_eval {s : ℕ} (d : State 5 s) (src dst : Fin s) (hsd : src ≠ dst) :
    ∃ time ≤ 6*(d.stacks src).length+2*(d.stacks dst).length+12, ∃ rf,
      Eval (lessClear src dst) time d
        (⟨rf,Function.update (Function.update d.stacks src []) dst []⟩ : State 5 s) ∧
      rf 3 = decide ((d.stacks src).length < (d.stacks dst).length) ∧
      rf 4 = d.regs 4 := by
  obtain ⟨time,ht,rr,l,r,h,hf,h4,hl,hr⟩ := lessAt_eval d src dst hsd
  let b : State 5 s := ⟨rr,Function.update (Function.update d.stacks src l) dst r⟩
  have h1 := clearAt_eval b src
  have h2 := clearAt_eval (clearedAt b src) dst
  let rf := (clearedAt (clearedAt b src) dst).regs
  have hs : clearedAt (clearedAt b src) dst =
      (⟨rf,Function.update (Function.update d.stacks src []) dst []⟩ : State 5 s) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hsi : i = src
      · subst i; simp [clearedAt,b,hsd]
      · by_cases hdi : i = dst
        · subst i; simp [clearedAt,b]
        · simp [clearedAt,b,hsi,hdi]
  have he := h.seq (h1.seq h2)
  change Eval (lessClear src dst)
    (time+((2*(b.stacks src).length+3)+(2*((clearedAt b src).stacks dst).length+3))) d
    (clearedAt (clearedAt b src) dst) at he
  rw [hs] at he
  refine ⟨_,?_,rf,he,?_,?_⟩
  · simp only [b,clearedAt,Function.update_apply,hsd,Ne.symm hsd,ite_false,ite_true]
    omega
  · simpa [rf,clearedAt,b,readRegs] using hf
  · simpa [rf,clearedAt,b,readRegs] using h4

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
