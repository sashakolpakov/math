import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateTraversal
import OAI.Algorithms.SubexponentialSAT.CounterPrograms

namespace OAI.Algorithms

/-! Actual bank-header extraction and the runtime color counter. -/

namespace SubexponentialSAT.SubexpRawTemplate

open BitProgram StructuredCalls SubexpScanPrimitives

def colorPorts : Fin 2 → Fin 288 := ![219, 218]
theorem colorPorts_injective : Function.Injective colorPorts := by decide

def incrementColor : Code :=
  .call (ProgramLinking.liftProgram (CounterPrograms.rippleProgram true) frameRegs colorPorts)

def incremented (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update d.stacks 219 (CounterPrograms.ripple true (d.stacks 219))⟩

theorem incrementColor_eval (d : Data) (h218 : d.stacks 218 = []) :
    Eval incrementColor (CounterPrograms.rippleCost true (d.stacks 219) + 1) d (incremented d) := by
  let a : State 3 2 := ⟨CounterPrograms.counterRegs (d.regs 0) (d.regs 1) (d.regs 2),
    CounterPrograms.counterStacks (d.stacks 219) []⟩
  let b : State 3 2 := ⟨CounterPrograms.counterRegs false false (d.regs 2),
    CounterPrograms.counterStacks (CounterPrograms.ripple true (d.stacks 219)) []⟩
  have ht : Trace (CounterPrograms.rippleProgram true)
      (CounterPrograms.rippleCost true (d.stacks 219))
      (a.withPC (some (CounterPrograms.rippleProgram true).entry)) (b.withPC (some 10)) := by
    simpa [a, b, CounterPrograms.counterCfg, CounterPrograms.rippleProgram] using
      CounterPrograms.ripple_trace true (d.regs 0) (d.regs 1) (d.regs 2) (d.stacks 219) []
  have hh : Trace (CounterPrograms.rippleProgram true) 1 (b.withPC (some 10)) (b.withPC none) :=
    .cons (by rfl) (.refl _)
  have hstart : embedState frameRegs colorPorts d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ frameRegs_injective colorPorts_injective
    · intro i
      fin_cases i <;> simp [a, frameRegs, CounterPrograms.counterRegs]
    · intros; rfl
    · intro i
      fin_cases i <;> simp [a, colorPorts, CounterPrograms.counterStacks, h218]
    · intros; rfl
  have hend : embedState frameRegs colorPorts d b = incremented d := by
    apply embedState_eq_of_ports _ _ _ _ _ frameRegs_injective colorPorts_injective
    · intro i
      fin_cases i <;> simp [b, frameRegs, incremented, readRegs, CounterPrograms.counterRegs]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      simp [incremented, readRegs, h0, h1]
    · intro i
      fin_cases i <;> simp [b, colorPorts, incremented, CounterPrograms.counterStacks, h218]
    · intro i hi
      have h219 : i ≠ 219 := fun h => hi ⟨0, h.symm⟩
      simp [incremented, h219]
  have he := eval_call_lifted (CounterPrograms.rippleProgram true) frameRegs colorPorts d
    frameRegs_injective colorPorts_injective (ht.trans hh)
  simpa only [incrementColor, hstart, hend] using he

theorem incrementColor_cost (d : Data) :
    CounterPrograms.rippleCost true (d.stacks 219) + 1 ≤ 8 * (d.stacks 219).length + 8 := by
  have h := CounterPrograms.rippleCost_le true (d.stacks 219)
  omega

def colorWord : ℕ → Word
  | 0 => []
  | n + 1 => CounterPrograms.ripple true (colorWord n)

@[simp] theorem colorWord_value (n : ℕ) : CounterPrograms.value (colorWord n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [colorWord, ih] using CounterPrograms.value_increment (colorWord n)

theorem colorWord_length (n : ℕ) : (colorWord n).length ≤ n := by
  induction n with
  | zero => simp [colorWord]
  | succ n ih =>
    have h := CounterPrograms.ripple_length_le true (colorWord n)
    simp only [colorWord]
    omega

def splitBanks : Code := .seq (popTag 204) (capture 204 205 (by decide))

def splitResult (outer inner : Word) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 204 inner) 205 outer⟩

/-- Consume the first actual bank-list record and leave the ordered inner
bank-list stream on204. The outer bank list is retained on205. -/
theorem splitBanks_eval (outer : Word) (inner : List Word) (d : Data)
    (h204 : d.stacks 204 = Encoding.encodeList id (outer :: inner))
    (h205 : d.stacks 205 = []) (h218 : d.stacks 218 = []) :
    Eval splitBanks (9 * outer.length + 8) d
      (splitResult outer (Encoding.encodeList id inner) d) := by
  let tail := Encoding.encodeList id inner
  let a := inputState 204 (readRegs d.regs 0 1 (some true)) d.stacks (Encoding.frame outer ++ tail)
  have hstart : inputState 204 d.regs d.stacks (true :: (Encoding.frame outer ++ tail)) = d := by
    apply state_ext
    · rfl
    · funext i
      by_cases hi : i = 204
      · subst i
        simpa [inputState, tail, Encoding.encodeList] using h204.symm
      · simp [inputState, hi]
  have hp := popTag_eval 204 d.regs d.stacks true (Encoding.frame outer ++ tail)
  rw [hstart] at hp
  have hc := capture_eval 204 205 (by decide) (by decide) (by decide) outer tail a
    (by simp [a, inputState]) (by simp [a, inputState, h205]) (by simp [a, inputState, h218])
  have hend : captured 204 205 outer tail a = splitResult outer tail d := by
    apply state_ext
    · funext i
      by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
        simp [captured, splitResult, a, inputState, readRegs, h0, h1]
    · funext i
      by_cases h204 : i = 204 <;> by_cases h205 : i = 205 <;>
        simp [captured, splitResult, a, inputState, h204, h205]
  have he := hp.seq hc
  rw [hend] at he
  change Eval splitBanks (1 + (9 * outer.length + 7)) d
    (splitResult outer tail d) at he
  have hcost : 1 + (9 * outer.length + 7) = 9 * outer.length + 8 := by
    omega
  rw [hcost] at he
  exact he

end SubexponentialSAT.SubexpRawTemplate

end OAI.Algorithms
