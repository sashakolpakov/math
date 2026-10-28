import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBankUnary
import OAI.Algorithms.SubexponentialSAT.CounterPredProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

def predPorts (a : Fin 64) : CounterForPrograms.Ports 8 77 where
  register := ⟨smallRegs, Fin.castAdd_injective 3 5⟩
  counter := port a
  scratch := work 1 (by decide) 0
  counter_ne_scratch := (work_ne_port 1 (by decide) 0 a).symm

abbrev predCmd (a : Fin 64) : Cmd 8 77 := CounterPredProgram.predCmd (predPorts a)

theorem pred_eval (r : Regs) (w : Words) (a : Fin 64) :
    ∃ t rf word, Eval (predCmd a) t (state r w)
        (state rf (Function.update w a word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a)-1 ∧ word.length ≤ (w a).length ∧
      t ≤ 20*((w a).length+1) := by
  obtain ⟨t,rf,word,ht,he,hv,hl⟩ := CounterPredProgram.pred_correct (predPorts a) (state r w)
    (state_work r w _ (by change 64 ≤ 64; omega))
  exact ⟨t,rf,word,by simpa only [predCmd,predPorts,state_update] using he,
    by simpa only [predPorts,state_port] using hv,
    by simpa only [predPorts,state_port] using hl,
    by simpa only [predPorts,state_port] using ht⟩

/-- Two saturating predecessors followed by two explicit increments implement
max(2,a), including padded zero words. -/
abbrev maxTwoCmd (a : Fin 64) : Cmd 8 77 :=
  .seq (predCmd a) (.seq (predCmd a) (addConstCmd a 2))

theorem maxTwo_eval (r : Regs) (w : Words) (a : Fin 64) :
    ∃ t rf word, Eval (maxTwoCmd a) t (state r w)
        (state rf (Function.update w a word)) ∧
      BinaryArithmetic.toNat word = max 2 (BinaryArithmetic.toNat (w a)) ∧ word.length ≤ (w a).length+2 ∧
      t ≤ 100*((w a).length+3) := by
  obtain ⟨t1,r1,v1,h1,hv1,hl1,ht1⟩ := pred_eval r w a
  let w1 := Function.update w a v1
  obtain ⟨t2,r2,v2,h2,hv2,hl2,ht2⟩ := pred_eval r1 w1 a
  let w2 := Function.update w1 a v2
  obtain ⟨t3,r3,v3,h3,hv3,hl3,ht3⟩ := addConst_eval r2 w2 a 2
  simp only [w1,w2,Function.update_self] at hv2 hl2 ht2 hv3 hl3 ht3
  refine ⟨t1+(t2+t3),r3,v3,?_,?_,by omega,by omega⟩
  · simpa only [maxTwoCmd,w2,w1,Function.update_idem] using h1.seq (h2.seq h3)
  · rw [hv3,hv2,hv1]
    omega

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
