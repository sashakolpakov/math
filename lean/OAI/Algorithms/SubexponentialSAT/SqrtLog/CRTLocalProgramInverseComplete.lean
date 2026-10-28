import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramInverseTrace

namespace OAI.Algorithms

/-! Complete native scalar inversion. The counter on 212 is independent of
the later polynomial-jet counter on 243. The only changed persistent port is
208. No inverse, residue-field enumeration, or ring-element enumeration is
an instruction of the compiled program. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def inverseBudget (exponent precision Km Ka W : ℕ) : ℕ :=
  (exponent + precision + 1) * (4*Km + 4*Ka + 300*W + 400)

theorem inverseCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (a zero one minusOne : C) (hf : LowFrame base s)
    (ha0 : s 205 = encode a) (hz0 : s 104 = encode zero)
    (ho0 : s 207 = encode one) (hn0 : s 211 = encode minusOne)
    (h120 : s 120 = []) (h208 : s 208 = [])
    (h220 : s 220 = []) (h222 : s 222 = [])
    (h240 : s 240 = []) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = []) :
    ExecutesIn (inverseCommand multiply add)
      (inverseBudget (s 209).length (s 212).length Km Ka W) s
      (Function.update s 208 (encode (inverseValue mulOp addOp zero one minusOne a
        (s 209).length (s 212).length))) := by
  let b := ((fun x => mulOp x a)^[(s 209).length] one)
  let z := defectValue mulOp addOp a b minusOne one
  let v := mulOp ((hornerValue mulOp addOp z one)^[(s 212).length] zero) b
  let s1 := seedState s encode a b
  let s2 := defectState s1 encode z one
  have hf1 : LowFrame base s1 :=
    lowFrame_update (lowFrame_update (lowFrame_update hf 240 (by decide) _)
      241 (by decide) _) 208 (by decide) _
  have hf2 : LowFrame base s2 :=
    lowFrame_update (lowFrame_update (lowFrame_update hf1 240 (by decide) _)
      241 (by decide) _) 222 (by decide) _
  have h1 : ExecutesIn (seedCommand multiply)
      (((s 209).length+1)*(Km+50*W+100)) s s1 :=
    seedCommand_run base encode multiply mulOp Km W hm hwidth s a one hf
      ha0 ho0 h120 h208 h240 h241 h244 h245 h246
  have h2 : ExecutesIn (defectCommand multiply add) (2*Km+Ka+60*W+60) s1 s2 :=
    defectCommand_run base encode multiply add mulOp addOp Km Ka W hm ha hwidth
      s1 a b minusOne one hf1
      (by simp [s1, seedState]) (by simp [s1, seedState])
      (by simp [s1, seedState, ho0]) (by simp [s1, seedState, hn0])
      (by simp [s1, seedState, h120]) (by simp [s1, seedState, h222])
      (by simp [s1, seedState, h244]) (by simp [s1, seedState, h245])
  have h3 : ExecutesIn (repairCommand multiply add)
      (((s 212).length+1)*(Km+Ka+150*W+200)) s2 (Function.update s 208 (encode v)) := by
    have h := repairCommand_run base encode multiply add mulOp addOp Km Ka W hm ha hwidth
      s2 z b zero one hf2
      (by simp [s2, defectState]) (by simp [s2, defectState])
      (by simp [s2, defectState, s1, seedState, ho0])
      (by simp [s2, defectState, s1, seedState, hz0])
      (by simp [s2, defectState, s1, seedState]) (by simp [s2, defectState])
      (by simp [s2, defectState, s1, seedState, h120])
      (by simp [s2, defectState, s1, seedState, h220])
      (by simp [s2, defectState, s1, seedState, h244])
      (by simp [s2, defectState, s1, seedState, h245])
      (by simp [s2, defectState, s1, seedState, h246])
    have hc : (s2 212).length = (s 212).length := by simp [s2, defectState, s1, seedState]
    rw [hc] at h
    have he : repairState s2 encode v = Function.update s 208 (encode v) := by
      funext i
      by_cases h220i : i = 220 <;> by_cases h222i : i = 222 <;>
        by_cases h240i : i = 240 <;> by_cases h241i : i = 241 <;> by_cases h208i : i = 208 <;>
        simp [repairState, SubexpLocalCRTSetup.cleared_apply, s2, defectState,
          s1, seedState, h220i, h222i, h240i, h241i,
          h220, h222, h240, h241, h208i]
    change ExecutesIn _ _ s2 (repairState s2 encode v) at h
    rw [he] at h
    exact h
  have h := h1.seq (h2.seq h3)
  apply h.mono
  dsimp only [inverseBudget]
  nlinarith

theorem inverseProgram_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (a zero one minusOne : C) (hf : LowFrame base s)
    (ha0 : s 205 = encode a) (hz0 : s 104 = encode zero)
    (ho0 : s 207 = encode one) (hn0 : s 211 = encode minusOne)
    (h120 : s 120 = []) (h208 : s 208 = [])
    (h220 : s 220 = []) (h222 : s 222 = [])
    (h240 : s 240 = []) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = [])
    (regs : Fin 16 → Bool) :
    ∃ finalRegs, RunsIn (inverseProgram multiply add)
      (inverseBudget (s 209).length (s 212).length Km Ka W + 1)
      ((⟨regs,s⟩ : Data).withPC (some (inverseProgram multiply add).entry))
      ((⟨finalRegs, Function.update s 208
        (encode (inverseValue mulOp addOp zero one minusOne a
          (s 209).length (s 212).length))⟩ : Data).withPC none) := by
  obtain ⟨n, finalRegs, hn, he⟩ := inverseCommand_run base encode multiply add mulOp addOp
    Km Ka W hm ha hwidth s a zero one minusOne hf ha0 hz0 ho0 hn0 h120 h208
    h220 h222 h240 h241 h244 h245 h246 regs
  exact ⟨finalRegs,n+1,by omega,compiled_halt_trace he 205 208⟩

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
