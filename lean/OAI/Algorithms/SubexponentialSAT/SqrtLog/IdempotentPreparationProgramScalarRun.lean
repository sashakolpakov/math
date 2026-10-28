import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramScalarBase

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Every operation and loop bound is read from the runtime stacks. -/
abbrev arithmeticCommand : Cmd 8 41 :=
  .seq (sequence constants) <|
  .seq (ArithmeticCalls.copyAt 29 40 38) <|
  .seq halfLoop <|
  .seq (sequence finalCoefficients) <|
  .seq (IdempotentProgram.registerClear 24) (IdempotentProgram.registerClear 25)

def finalValues (t:ℕ) (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t) : Values 3 t :=
  run 3 t M finalCoefficients (iterateForward 3 t M (run 3 t M constants v) t)

def Output (t:ℕ) (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t) (d:Data) : Prop :=
  Rest d M.bits ∧ d.stacks 24=[] ∧ d.stacks 25=[] ∧
    ∀i:Reg,i≠6→i≠7→d.stacks (port i)=(v i).val

theorem arithmeticCommand_eval (t:ℕ) (M:SubexpPreparedQuartic.Modulus 3 t)
    (v:Values 3 t) (d:Data) (h:Encoded 3 t M v d)
    (h29:d.stacks 29=List.replicate t true) (h40:d.stacks 40=[]) :
    ∃ n e, Eval arithmeticCommand n d e ∧ Output t M (finalValues t M v) e ∧
      Frame d e ∧
      n ≤ (3*t+10)*stepBudget 3 t+9*t+4*baseWidth 3 t+13 := by
  obtain ⟨n1,a,ha,hva,hfa,hn1⟩:=sequence_eval 3 t M constants v d h
  have ha29:a.stacks 29=List.replicate t true := by
    rw [hfa 29 (by intro i; fin_cases i <;> decide)]; exact h29
  have ha40:a.stacks 40=[] := by rw [hfa 40 port_ne40]; exact h40
  let b:=ArithmeticCalls.afterCopy 29 40 a
  have cp:=ArithmeticCalls.copyAt_eval (29:Fin 41) 40 38 a (by decide) (by decide)
    (by decide) ha40 hva.1.2
  have hbs:b.stacks=Function.update a.stacks 40 (List.replicate t true) := by
    simp [b,ArithmeticCalls.afterCopy,ha29]
  have hvb:Encoded 3 t M (run 3 t M constants v) b := by
    constructor
    · constructor
      · intro i
        have hi:low i≠40 := by intro hh; have hv:=congrArg Fin.val hh; dsimp [low] at hv; omega
        simpa [hbs,hi] using hva.1.1 i
      · simpa [hbs] using hva.1.2
    · intro i; simpa [hbs,port_ne40] using hva.2 i
  obtain ⟨n2,c,hc,hvc,hc40,hfc,hn2⟩:=halfLoop_eval 3 t M _ b hvb
  have hblen:(b.stacks 40).length=t := by simp [hbs]
  rw [hblen] at hvc hn2
  obtain ⟨n3,f,hf,hvf,hff,hn3⟩:=sequence_eval 3 t M finalCoefficients _ c hvc
  have f24:(f.stacks 24).length=baseWidth 3 t := by
    have hh:=hvf.2 6
    exact (congrArg List.length hh).trans ((run 3 t M finalCoefficients (iterateForward 3 t M (run 3 t M constants v) t) 6).property)
  have f25:(f.stacks 25).length=baseWidth 3 t := by
    have hh:=hvf.2 7
    exact (congrArg List.length hh).trans ((run 3 t M finalCoefficients (iterateForward 3 t M (run 3 t M constants v) t) 7).property)
  let g:=IdempotentProgram.cleared f 24
  let e:=IdempotentProgram.cleared g 25
  have cl1:=IdempotentProgram.registerClear_eval f 24
  have cl2:=IdempotentProgram.registerClear_eval g 25
  refine ⟨_,e,ha.seq (cp.seq (hc.seq (hf.seq (cl1.seq cl2)))),?_,?_,?_⟩
  · refine ⟨?_,by simp [e,g,IdempotentProgram.cleared],by simp [e,IdempotentProgram.cleared],?_⟩
    · constructor
      · intro i
        have h24:low i≠24 := by intro hh; have hv:=congrArg Fin.val hh; dsimp [low] at hv; omega
        have h25:low i≠25 := by intro hh; have hv:=congrArg Fin.val hh; dsimp [low] at hv; omega
        simpa [e,g,IdempotentProgram.cleared,h24,h25] using hvf.1.1 i
      · simpa [e,g,IdempotentProgram.cleared] using hvf.1.2
    · intro i hi6 hi7
      have hi24:port i≠24 := by intro hh; exact hi6 (port_injective hh)
      have hi25:port i≠25 := by intro hh; exact hi7 (port_injective hh)
      simpa [e,g,IdempotentProgram.cleared,hi24,hi25,finalValues] using hvf.2 i
  · intro j hj
    have hj24:j≠24 := (hj 6).symm
    have hj25:j≠25 := (hj 7).symm
    simp only [e,g,IdempotentProgram.cleared,Function.update_of_ne hj25,Function.update_of_ne hj24]
    rw [hff j hj]
    by_cases hj40:j=40
    · subst j; rw [hc40,h40]
    · rw [hfc j hj40 hj,hbs,Function.update_of_ne hj40,hfa j hj]
  · simp only [constants,List.length_cons,List.length_nil] at hn1
    simp only [finalCoefficients,List.length_cons,List.length_nil] at hn3
    simp only [g,IdempotentProgram.cleared,Function.update_of_ne (by decide : (25:Fin 41)≠24),
      f24,f25,ha29,List.length_replicate]
    nlinarith

abbrev command : Cmd 8 41 := .seq baseCommand arithmeticCommand

theorem command_eval (t:ℕ) (M:SubexpPreparedQuartic.Modulus 3 t)
    (shape:List Bool) (hs:shape.length=baseWidth 3 t) (d:Data) (W:ℕ)
    (h:Rest d M.bits) (h12:d.stacks 12=shape) (hW:shape.length ≤ W)
    (hslots:∀i,(d.stacks (port i)).length ≤ W)
    (h29:d.stacks 29=List.replicate t true) (h40:d.stacks 40=[]) :
    ∃ n e, Eval command n d e ∧
      Output t M (finalValues t M (baseValues t M shape hs)) e ∧ Frame d e ∧
      n ≤ 400*(baseWidth 3 t+W+1)+(3*t+10)*stepBudget 3 t+9*t+4*baseWidth 3 t+13 := by
  obtain ⟨n1,a,ha,hva,hfa,hn1⟩:=baseCommand_eval t M shape hs d W h h12 hW hslots
  have ha29:a.stacks 29=List.replicate t true := by
    rw [hfa 29 (by intro i; fin_cases i <;> decide)]; exact h29
  have ha40:a.stacks 40=[] := by rw [hfa 40 port_ne40]; exact h40
  obtain ⟨n2,e,he,hve,hfe,hn2⟩:=arithmeticCommand_eval t M _ a hva ha29 ha40
  exact ⟨n1+n2,e,ha.seq he,hve,fun j hj=>(hfe j hj).trans (hfa j hj),by omega⟩

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
