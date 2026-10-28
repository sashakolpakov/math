import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramLog
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

open BitProgram StructuredCalls
open BinaryArithmetic (toNat)

abbrev PrecisionData := StructuredProgram.State 8 10

def logRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def logStacks : Fin 3 → Fin 10 := ![8, 3, 4]

theorem logRegisters_injective : Function.Injective logRegisters := Fin.castAdd_injective _ _
theorem logStacks_injective : Function.Injective logStacks := by decide

abbrev logCall : Cmd 8 10 :=
  liftCommand logSizeSuccCommand 0 0 logRegisters logStacks

theorem logCall_eval (d : PrecisionData) (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = []) :
    ∃ t rf word,
      Eval logCall t d ⟨rf, Function.update d.stacks 8 word⟩ ∧
      BinaryArithmetic.toNat word = Nat.log2 (BinaryArithmetic.toNat (d.stacks 8)) + 2 ∧
      word.length ≤ (d.stacks 8).length + 2 ∧
      t ≤ 65 * ((d.stacks 8).length + 2)^2 := by
  have hst : (projectState logRegisters logStacks d).stacks = (Setup.io (d.stacks 8)).stacks := by
    funext i; fin_cases i <;> simp [projectState,logStacks,h3,h4]
  obtain ⟨word,t,hv,hl,ht,he⟩ :=
    logSizeSuccCommand_eval (d.stacks 8) (projectState logRegisters logStacks d) hst
  let e := embedState logRegisters logStacks d (Setup.io word)
  have hr : Eval logCall (t+1) d e :=
    eval_liftCommand_from_state logSizeSuccCommand 0 0 logRegisters logStacks d
      logRegisters_injective logStacks_injective he
  have hw : (Setup.io word).stacks =
      Function.update (projectState logRegisters logStacks d).stacks 0 word := by
    rw [hst]
    funext i; fin_cases i <;> simp []
  have hs : e.stacks = Function.update d.stacks 8 word := by
    change Function.extend logStacks (Setup.io word).stacks d.stacks = _
    rw [hw,ProgramLinking.extend_update logStacks_injective]
    have hx : Function.extend logStacks (projectState logRegisters logStacks d).stacks d.stacks =
        d.stacks := congrArg StructuredProgram.State.stacks
          (embedState_project logRegisters logStacks d logRegisters_injective logStacks_injective)
    rw [hx]
    rfl
  have heq : e = ⟨e.regs, Function.update d.stacks 8 word⟩ := by
    exact CounterForPrograms.data_ext rfl hs
  refine ⟨t+1,e.regs,word,?_,?_,hl,by nlinarith⟩
  · rw [← heq]
    exact hr
  · simpa only [SubexpParameterProgram.value_eq_toNat] using hv

def precisionWork : Fin 5 ↪ Fin 10 where
  toFun i := ⟨i.val + 3, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

def precisionAdd : ArithmeticCalls.Ports 10 where
  left := 0
  right := 8
  out := 2
  work := precisionWork
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

/-- Preserve ambient and clause-count words; output the precision on port 2. -/
abbrev precisionCommand : Cmd 8 10 :=
  .seq (ArithmeticCalls.copyAt 1 8 9)
    (.seq logCall (.seq (ArithmeticCalls.addAt precisionAdd)
      (ArithmeticExpressionSupport.clearCmd 8)))

def precisionReady (d : PrecisionData) : Prop :=
  ∀ j : Fin 10, 2 ≤ j.val → d.stacks j = []

theorem precisionCommand_eval (d : PrecisionData) (hd : precisionReady d)
    (hm : BinaryArithmetic.toNat (d.stacks 1) ≠ 0) :
    ∃ t rf word,
      Eval precisionCommand t d ⟨rf, Function.update d.stacks 2 word⟩ ∧
      BinaryArithmetic.toNat word = precision (BinaryArithmetic.toNat (d.stacks 0)) (BinaryArithmetic.toNat (d.stacks 1)) ∧
      word.length ≤ (d.stacks 0).length + (d.stacks 1).length + 3 ∧
      t ≤ 1000 * ((d.stacks 0).length + (d.stacks 1).length + 3)^2 := by
  have hc := ArithmeticCalls.copyAt_eval (1 : Fin 10) 8 9 d
    (by decide) (by decide) (by decide) (hd 8 (by decide)) (hd 9 (by decide))
  let a := ArithmeticCalls.afterCopy 1 8 d
  obtain ⟨tl,rl,wl,hel,hvl,hll,htl⟩ := logCall_eval a
    (by simp [a,ArithmeticCalls.afterCopy,hd 3 (by decide)])
    (by simp [a,ArithmeticCalls.afterCopy,hd 4 (by decide)])
  let b : PrecisionData := ⟨rl,Function.update a.stacks 8 wl⟩
  have hb : b.stacks = Function.update d.stacks 8 wl := by
    simp [b,a,ArithmeticCalls.afterCopy]
  have hva : ArithmeticCalls.Valid precisionAdd b := by
    constructor
    · simp [precisionAdd,hb,hd 2 (by decide)]
    · intro i
      have hi : precisionWork i ≠ 8 := precisionAdd.work_ne_right i
      change b.stacks (precisionWork i) = []
      rw [hb,Function.update_of_ne hi]
      exact hd (precisionWork i) (by change 2 ≤ i.val + 3; omega)
  obtain ⟨ta,ra,wa,hea,hva,hla,hta⟩ := ArithmeticCalls.addAt_eval precisionAdd b hva
  let c : PrecisionData := ⟨ra,Function.update b.stacks 2 wa⟩
  have hcl := ArithmeticExpressionSupport.clear_eval (8 : Fin 10) c
  let e : PrecisionData := ⟨readRegs c.regs 0 1 none,Function.update c.stacks 8 []⟩
  have hs : e.stacks = Function.update d.stacks 2 wa := by
    funext i
    by_cases h8 : i=8
    · subst i; simp [e,c,hb,hd 8 (by decide)]
    · by_cases h2 : i = 2
      · subst i; simp only [e,c,Function.update_of_ne (by decide : (2 : Fin 10) ≠ 8),Function.update_self]
      · simp only [e,c,hb,Function.update_of_ne h8,Function.update_of_ne h2]
  have heq : e = ⟨e.regs, Function.update d.stacks 2 wa⟩ := CounterForPrograms.data_ext rfl hs
  have hcl' : Eval (ArithmeticExpressionSupport.clearCmd 8) (2*wl.length+3) c e := by
    simpa [e,c,hb] using hcl
  have hc' : Eval (ArithmeticCalls.copyAt 1 8 9) (7*(d.stacks 1).length+5) d a := hc
  have hel' : Eval logCall tl a b := hel
  have hea' : Eval (ArithmeticCalls.addAt precisionAdd) ta b c := hea
  refine ⟨7*(d.stacks 1).length+5+(tl+(ta+(2*wl.length+3))),e.regs,wa,?_,?_,?_,?_⟩
  · rw [← heq]
    exact hc'.seq (hel'.seq (hea'.seq hcl'))
  · simp only [precisionAdd,hb,Function.update_same,
      Function.update_noteq (by decide : (0 : Fin 10) ≠ 8)] at hva
    simp [a,ArithmeticCalls.afterCopy] at hvl
    rw [hva,hvl,precision,size_eq_log2_add_one hm]
    omega
  · simp [precisionAdd,hb] at hla
    simp [a,ArithmeticCalls.afterCopy] at hll
    omega
  · simp [precisionAdd,hb] at hta
    simp [a,ArithmeticCalls.afterCopy] at hll htl
    have hlen : (d.stacks 0).length + wl.length + 1 ≤
        (d.stacks 0).length + (d.stacks 1).length + 3 := by omega
    have hpow := Nat.pow_le_pow_left hlen 2
    nlinarith

def precisionProgram := compiled precisionCommand 0 2

theorem precisionProgram_runs (d : PrecisionData) (hd : precisionReady d)
    (hm : BinaryArithmetic.toNat (d.stacks 1) ≠ 0) :
    ∃ rf word, RunsIn precisionProgram
      (1001*((d.stacks 0).length+(d.stacks 1).length+3)^2)
      (d.withPC (some precisionProgram.entry))
      ((⟨rf,Function.update d.stacks 2 word⟩ : PrecisionData).withPC none) ∧
      BinaryArithmetic.toNat word = precision (BinaryArithmetic.toNat (d.stacks 0)) (BinaryArithmetic.toNat (d.stacks 1)) := by
  obtain ⟨t,rf,word,he,hv,hl,ht⟩ := precisionCommand_eval d hd hm
  exact ⟨rf,word,⟨t+1,by nlinarith,compiled_halt_trace he 0 2⟩,hv⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
