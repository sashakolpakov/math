import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBank
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramLog

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

def smallRegs : Fin 3 → Fin 8 := Fin.castAdd 5

def unaryStacks (a : Fin 64) : Fin 3 → Fin 77 :=
  ![port a, work 2 (by decide) 0, work 2 (by decide) 1]

theorem unaryStacks_injective (a : Fin 64) : Function.Injective (unaryStacks a) := by
  have h0 := work_ne_port 2 (by decide) (0 : Fin 2) a
  have h1 := work_ne_port 2 (by decide) (1 : Fin 2) a
  have h01 : work 2 (by decide) (0 : Fin 2) ≠ work 2 (by decide) (1 : Fin 2) := by
    intro h
    exact Fin.zero_ne_one ((work 2 (by decide)).injective h)
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [unaryStacks]

abbrev unaryCmd (a : Fin 64) (body : Cmd 3 3) : Cmd 8 77 :=
  liftCommand (.seq resetLog body) 0 0 smallRegs (unaryStacks a)

/-- A real three-stack word routine is relocated into the numeric bank. The
four administrative steps reset its Boolean registers and invoke its finite
instruction table; all numeric work remains charged in `cost`. -/
theorem unary_eval (r : Regs) (w : Words) (a : Fin 64) (body : Cmd 3 3)
    (f lengthBound cost : List Bool → ℕ)
    (hspec : ∀ xs, ∃ word t, BinaryArithmetic.toNat word = f xs ∧ word.length ≤ lengthBound xs ∧
      t ≤ cost xs ∧ Eval body t (Setup.io xs) (Setup.io word)) :
    ∃ t rf word, Eval (unaryCmd a body) t (state r w)
        (state rf (Function.update w a word)) ∧
      BinaryArithmetic.toNat word = f (w a) ∧ word.length ≤ lengthBound (w a) ∧ t ≤ cost (w a)+4 := by
  let d := state r w
  let a0 : LogData := projectState smallRegs (unaryStacks a) d
  have hst : a0.stacks = (Setup.io (w a)).stacks := by
    funext i
    fin_cases i
    · simp [a0, projectState, unaryStacks, d, state_port]
    · simpa [a0, projectState, unaryStacks, d, Setup.io,
        StructuredProgram.ioState] using
        (state_work r w (work 2 (by decide) 0) (by rw [work_val]; omega))
    · simpa [a0, projectState, unaryStacks, d, Setup.io,
        StructuredProgram.ioState] using
        (state_work r w (work 2 (by decide) 1) (by rw [work_val]; omega))
  obtain ⟨word,t,hv,hl,ht,he⟩ := hspec (w a)
  have hr : Eval resetLog 3 a0 (Setup.io (w a)) := by
    simpa only [hst] using resetLog_eval a0
  let e := embedState smallRegs (unaryStacks a) d (Setup.io word)
  have hh : Eval (unaryCmd a body) ((3+t)+1) d e :=
    eval_liftCommand_from_state (.seq resetLog body) 0 0 smallRegs (unaryStacks a) d
      (Fin.castAdd_injective 3 5) (unaryStacks_injective a) (hr.seq he)
  have hw : (Setup.io word).stacks = Function.update a0.stacks 0 word := by
    rw [hst]
    funext i; fin_cases i <;> simp []
  have hes : e.stacks = Function.update d.stacks (port a) word := by
    change Function.extend (unaryStacks a) (Setup.io word).stacks d.stacks = _
    rw [hw,ProgramLinking.extend_update (unaryStacks_injective a)]
    have hx : Function.extend (unaryStacks a) a0.stacks d.stacks = d.stacks :=
      congrArg StructuredProgram.State.stacks
        (embedState_project smallRegs (unaryStacks a) d
          (Fin.castAdd_injective 3 5) (unaryStacks_injective a))
    rw [hx]
    rfl
  have heq : e = state e.regs (Function.update w a word) := by
    rw [← state_update r e.regs w a word]
    exact CounterForPrograms.data_ext rfl hes
  refine ⟨(3+t)+1,e.regs,word,?_,hv,hl,by omega⟩
  rw [← heq]
  exact hh

def logSuccCmd (a : Fin 64) := unaryCmd a Setup.logSucc

theorem logSucc_eval (r : Regs) (w : Words) (a : Fin 64) :
    ∃ t rf word, Eval (logSuccCmd a) t (state r w)
        (state rf (Function.update w a word)) ∧
      BinaryArithmetic.toNat word = Nat.log2 (BinaryArithmetic.toNat (w a))+1 ∧ word.length ≤ (w a).length+1 ∧
      t ≤ 32*((w a).length+1)^2+4 := by
  apply unary_eval r w a Setup.logSucc
    (fun xs => Nat.log2 (BinaryArithmetic.toNat xs)+1) (fun xs => xs.length+1)
    (fun xs => 32*(xs.length+1)^2)
  intro xs
  simpa only [CounterPrograms.value_eq_toNat] using Setup.logSucc_eval xs

def addConstCmd (a : Fin 64) (k : ℕ) := unaryCmd a (Setup.addConst k)

theorem addConst_eval (r : Regs) (w : Words) (a : Fin 64) (k : ℕ) :
    ∃ t rf word, Eval (addConstCmd a k) t (state r w)
        (state rf (Function.update w a word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a)+k ∧ word.length ≤ (w a).length+k ∧
      t ≤ 8*k*((w a).length+k+1)+4 := by
  apply unary_eval r w a (Setup.addConst k)
    (fun xs => BinaryArithmetic.toNat xs+k) (fun xs => xs.length+k)
    (fun xs => 8*k*(xs.length+k+1))
  intro xs
  simpa only [CounterPrograms.value_eq_toNat] using Setup.addConst_eval k xs

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
