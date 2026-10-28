import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRowToTaylor
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! The 25-register, 288-stack row service. Sixteen actual register resets
allow arbitrary caller registers; the surrounding registers and stacks are
framed. The consumed source is cleared from 26 and the full row goes to 87. -/

namespace SubexponentialSAT.SubexpRowToTaylorCalls

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing
open SubexpRowPostfixInterpreter (physicalCfg contextStore)

abbrev Data := StructuredProgram.State 25 288

def register : Fin 16 → Fin 25 := Fin.castAdd 9
def stack : Fin 256 → Fin 288 := Fin.castAdd 32

theorem register_injective : Function.Injective register := Fin.castAdd_injective _ _
theorem stack_injective : Function.Injective stack := Fin.castAdd_injective _ _

def resetPorts : List (Fin 25) := (List.finRange 16).map register
abbrev reset : Cmd 25 288 := RegisterResetProgram.clear resetPorts
def resetState (a : Data) : Data := RegisterResetProgram.cleared resetPorts a
abbrev call : Cmd 25 288 :=
  .call (ProgramLinking.liftProgram SubexpRowToTaylor.program register stack)
abbrev command : Cmd 25 288 := .seq reset call
def program := compiled command 26 87

theorem reset_eval (a : Data) : Eval reset 16 a (resetState a) := by
  simpa only [reset, resetState, resetPorts, List.length_map, List.length_finRange] using
    RegisterResetProgram.clear_eval resetPorts a

theorem reset_register (a : Data) (i : Fin 16) : (resetState a).regs (register i) = false := by
  have hi : register i ∈ resetPorts := List.mem_map.mpr ⟨i, by simp, rfl⟩
  simp [resetState, RegisterResetProgram.cleared, hi]

noncomputable def finished (a : Data) (rf : Fin 16 → Bool) (bits : List Bool) : Data :=
  ⟨Function.extend register rf (resetState a).regs,
    Function.update (Function.update a.stacks 26 []) 87 bits⟩

def code {p : ℕ} (e : Algorithm.Expr (List (SubexpRowPolynomialCalls.Coefficient p 1))) : List Bool :=
  SubexpPostfixControl.serializeCode SubexpRowPolynomialCalls.encode e.compile

def evaluated {p : ℕ} [Fact p.Prime] (source : SubexpSelectedConversions.Prepared p 0)
    (R : ℕ) (e : Algorithm.Expr (List (SubexpRowPolynomialCalls.Coefficient p 1))) :
    List (SubexpRowPolynomialCalls.Coefficient p 1) :=
  letI : Add (List (SubexpRowPolynomialCalls.Coefficient p 1)) :=
    ⟨SubexpRowPostfixBridge.addValue source.program⟩
  letI : Mul (List (SubexpRowPolynomialCalls.Coefficient p 1)) :=
    ⟨SubexpRowPostfixBridge.mulValue p 1 source.modulus source.reduction source.zero (R + 1)⟩
  (e.map (SubexpRowPostfixBridge.loadValue source.zero (R + 1))).eval

def output {p : ℕ} [Fact p.Prime] (μ : ℕ) (source : SubexpSelectedConversions.Prepared p 0)
    (R : ℕ) (e : Algorithm.Expr (List (SubexpRowPolynomialCalls.Coefficient p 1))) : List Bool :=
  (SubexpCoefficientLiftArray.encodeArray
    (SubexpCoefficientLiftArray.liftedArray p μ source.modulus (evaluated source R e))).reverse

theorem output_length {p : ℕ} [Fact p.Prime] (μ : ℕ)
    (source : SubexpSelectedConversions.Prepared p 0) (R : ℕ)
    (e : Algorithm.Expr (List (SubexpRowPolynomialCalls.Coefficient p 1))) :
    (output μ source R e).length = (R + 1) * (4 * baseWidth p μ) := by
  simp only [output, List.length_reverse]
  exact SubexpRowToTaylor.output_length p μ source R e

private theorem clear_source (source : List Bool) (context : Fin 252 → List Bool) :
    contextStore context = Function.update
      (physicalCfg (l := 1) none false false false source [] [] context).stacks 26 [] := by
  funext i
  by_cases h26 : i = 26
  · subst i; simp [contextStore]
  by_cases h28 : i = 28
  · subst i; simp [contextStore]
  by_cases h27 : i = 27
  · subst i; simp [contextStore]
  rw [Function.update_of_ne h26]
  exact (SubexpRowPostfixInterpreter.physicalCfg_frame _ _ _ _ _ _ _ _ _ h26 h28 h27).symm

variable (p μ : ℕ) [Fact p.Prime] (source : SubexpSelectedConversions.Prepared p 0) (R : ℕ)
variable (sw tw : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)

theorem command_eval (hμ : 0 < μ)
    (H : SubexpRowPostfixContext.Ready p 1 source.modulus source.reduction source.zero
      (R + 1) sw frame context)
    (hz : SubexpFlatAdd.encode source.zero = List.replicate (4 * baseWidth p 1) false)
    (h74 : contextStore context 74 = tw) (h87 : contextStore context 87 = [])
    (hB : tw.length = baseWidth p μ)
    (e : Algorithm.Expr (List (SubexpRowPolynomialCalls.Coefficient p 1)))
    (a : Data)
    (hstore : ∀ i, a.stacks (stack i) =
      (physicalCfg (l := 1) none false false false (code e) [] [] context).stacks i) :
    ∃ n rf, n ≤ 16 + SubexpRowToTaylor.runtimeBound R (baseWidth p 1) (baseWidth p μ) (code e).length ∧
      Eval command n a (finished a rf (output μ source R e)) := by
  obtain ⟨rf, n, hn, ht⟩ :=
    SubexpRowToTaylor.run_bounded p μ source R sw tw frame context hμ H hz h74 h87 hB e
  let start : StructuredProgram.State 16 256 := ⟨fun _ => false,
    (physicalCfg (l := 1) none false false false (code e) [] [] context).stacks⟩
  let stop : StructuredProgram.State 16 256 :=
    ⟨rf, Function.update (contextStore context) 87 (output μ source R e)⟩
  have hstart : physicalCfg (some SubexpRowToTaylor.program.entry) false false false
      (code e) [] [] context = start.withPC (some SubexpRowToTaylor.program.entry) := by
    apply congrArg₂ (Cfg.mk (some SubexpRowToTaylor.program.entry))
    · exact SubexpRowPostfixInterpreter.physicalCfg_false_regs
        (some SubexpRowToTaylor.program.entry) (code e) [] [] context
    · rfl
  change Trace SubexpRowToTaylor.program n
    (physicalCfg (some SubexpRowToTaylor.program.entry) false false false (code e) [] [] context)
    (stop.withPC none) at ht
  rw [hstart] at ht
  have hin : embedState register stack (resetState a) start = resetState a := by
    apply embedState_eq_of_ports _ _ _ _ _ register_injective stack_injective
    · exact reset_register a
    · intros; rfl
    · exact hstore
    · intros; rfl
  have hs : Function.extend stack start.stacks a.stacks = a.stacks := by
    exact congrArg StructuredProgram.State.stacks hin
  have hout : embedState register stack (resetState a) stop =
      finished a rf (output μ source R e) := by
    apply congrArg (StructuredProgram.State.mk _)
    change Function.extend stack
      (Function.update (contextStore context) 87 (output μ source R e)) a.stacks = _
    rw [clear_source (code e) context,
      ProgramLinking.extend_update stack_injective,
      ProgramLinking.extend_update stack_injective, hs]
    rfl
  have he := eval_call_lifted SubexpRowToTaylor.program register stack
    (resetState a) register_injective stack_injective ht
  have hc : Eval call n (resetState a) (finished a rf (output μ source R e)) := by
    simpa only [call, hin, hout] using he
  exact ⟨16 + n, rf, Nat.add_le_add_left hn 16, (reset_eval a).seq hc⟩

theorem program_run (hμ : 0 < μ)
    (H : SubexpRowPostfixContext.Ready p 1 source.modulus source.reduction source.zero
      (R + 1) sw frame context)
    (hz : SubexpFlatAdd.encode source.zero = List.replicate (4 * baseWidth p 1) false)
    (h74 : contextStore context 74 = tw) (h87 : contextStore context 87 = [])
    (hB : tw.length = baseWidth p μ)
    (e : Algorithm.Expr (List (SubexpRowPolynomialCalls.Coefficient p 1)))
    (a : Data)
    (hstore : ∀ i, a.stacks (stack i) =
      (physicalCfg (l := 1) none false false false (code e) [] [] context).stacks i) :
    ∃ rf, RunsIn program
      (17 + SubexpRowToTaylor.runtimeBound R (baseWidth p 1) (baseWidth p μ) (code e).length)
      (a.withPC (some program.entry)) ((finished a rf (output μ source R e)).withPC none) := by
  obtain ⟨n, rf, hn, ht⟩ := command_eval p μ source R sw tw frame context
    hμ H hz h74 h87 hB e a hstore
  exact ⟨rf, n + 1, by omega, compiled_halt_trace ht 26 87⟩

theorem finished_frame (a : Data) (rf : Fin 16 → Bool) (bits : List Bool) (i : Fin 288)
    (h26 : i ≠ 26) (h87 : i ≠ 87) : (finished a rf bits).stacks i = a.stacks i := by
  simp [finished, h26, h87]

theorem finished_register_frame (a : Data) (rf : Fin 16 → Bool) (bits : List Bool) (i : Fin 25)
    (hi : ¬ ∃ j, register j = i) : (finished a rf bits).regs i = a.regs i := by
  rw [show (finished a rf bits).regs i =
      Function.extend register rf (resetState a).regs i from rfl,
    Function.extend_apply' _ _ _ hi]
  have hn : i ∉ resetPorts := by
    intro h
    obtain ⟨j, _, hj⟩ := List.mem_map.mp h
    exact hi ⟨j, hj⟩
  simp [resetState, RegisterResetProgram.cleared, hn]

@[simp] theorem finished_output (a : Data) (rf : Fin 16 → Bool) (bits : List Bool) :
    (finished a rf bits).stacks 87 = bits := by simp [finished]

@[simp] theorem finished_source (a : Data) (rf : Fin 16 → Bool) (bits : List Bool) :
    (finished a rf bits).stacks 26 = [] := by simp [finished]

end SubexponentialSAT.SubexpRowToTaylorCalls

end OAI.Algorithms
