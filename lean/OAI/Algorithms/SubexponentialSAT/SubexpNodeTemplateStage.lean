import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateProgram
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCacheSetup
import OAI.Algorithms.SubexponentialSAT.SubexpNodeMomentLoop

namespace OAI.Algorithms

/-!
# A disjoint node-template workspace and physical cache cleanup

The actual 142-port template program is relocated as a whole. Its result139
lands directly on the job generator's template master200. The native trace
premise below is the explicit producer obligation until TemplateProgram's
execution theorem is installed; no prepared template is supplied by oracle.
-/

namespace SubexponentialSAT.SubexpNodeTemplateStage

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 256

def lowPort : Fin 25 → Fin 256 :=
  ![0,1,2,3,4,6,7,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,26,27]

theorem lowPort_injective : Function.Injective lowPort := by decide

theorem lowPort_le (i : Fin 25) : (lowPort i).val ≤ 27 := by
  fin_cases i <;> decide

def basePort (i : Fin 142) : Fin 256 :=
  if h : i.val < 117 then ⟨138 + i.val, by omega⟩
  else lowPort ⟨i.val - 117, by omega⟩

theorem basePort_injective : Function.Injective basePort := by
  intro i j he
  by_cases hi : i.val < 117
  · by_cases hj : j.val < 117
    · apply Fin.ext
      have hv := congrArg Fin.val he
      simp only [basePort, dite_eq_left hi, dite_eq_left hj] at hv
      omega
    · have hv := congrArg Fin.val he
      simp only [basePort, dite_eq_left hi, dite_eq_right hj] at hv
      have hb := lowPort_le ⟨j.val - 117, by omega⟩
      omega
  · by_cases hj : j.val < 117
    · have hv := congrArg Fin.val he
      simp only [basePort, dite_eq_right hi, dite_eq_left hj] at hv
      have hb := lowPort_le ⟨i.val - 117, by omega⟩
      omega
    · simp only [basePort, dite_eq_right hi, dite_eq_right hj] at he
      have hv := congrArg Fin.val (lowPort_injective he)
      apply Fin.ext
      dsimp only at hv
      omega

def port : Fin 142 → Fin 256 := basePort ∘ Equiv.swap 62 139
def registers : Fin 8 → Fin 16 := Fin.castAdd 8

theorem port_injective : Function.Injective port :=
  basePort_injective.comp (Equiv.swap 62 139).injective

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _

@[simp] theorem port_input : port 130 = 15 := by decide
@[simp] theorem port_output : port 139 = 200 := by decide

/-- This contains every target, row-cache, and source-cache master which
must survive the template call. Only low scratch and138--254 are used. -/
def Protected (i : Fin 256) : Prop :=
  (28 ≤ i.val ∧ i.val < 138) ∨ i = 5 ∨ i = 10 ∨ i = 25 ∨ i = 255

theorem lowPort_not_protected (i : Fin 25) : ¬ Protected (lowPort i) := by
  fin_cases i <;> unfold Protected <;> decide

theorem basePort_ne_protected (i : Fin 142) (j : Fin 256) (hj : Protected j) :
    basePort i ≠ j := by
  intro he
  by_cases hi : i.val < 117
  · have hv := congrArg Fin.val he
    simp only [basePort, dite_eq_left hi] at hv
    simp only [Protected, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hj
    omega
  · have he' : lowPort ⟨i.val - 117, by omega⟩ = j := by
      simpa only [basePort, dite_eq_right hi] using he
    exact lowPort_not_protected _ (he'.symm ▸ hj)

theorem port_ne_protected (i : Fin 142) (j : Fin 256) (hj : Protected j) : port i ≠ j :=
  basePort_ne_protected _ j hj

def localState (d : Data) : SubexpTemplateProgram.Data :=
  ⟨d.regs ∘ registers, d.stacks ∘ port⟩

abbrev templateCall : Cmd 16 256 :=
  .call (ProgramLinking.liftProgram SubexpTemplateProgram.program registers port)

abbrev command : Cmd 16 256 := .seq templateCall SubexpNodeCacheSetup.cleanup
abbrev program : Program 16 256 (size command + 1) := compiled command 15 200
def stage : SubexpNodeMomentLoop.Stage := ⟨_, program⟩

theorem localState_embed (d : Data) :
    embedState registers port d (localState d) = d := by
  apply embedState_eq _ _ registers_injective port_injective
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl

theorem template_eval (d : Data) (out : SubexpTemplateProgram.Data) (n : ℕ)
    (h : Trace SubexpTemplateProgram.program n
      ((localState d).withPC (some SubexpTemplateProgram.program.entry)) (out.withPC none)) :
    Eval templateCall n d (embedState registers port d out) := by
  have he := eval_call_lifted SubexpTemplateProgram.program registers port d
    registers_injective port_injective h
  simpa only [templateCall, localState_embed] using he

theorem template_frame (d : Data) (out : SubexpTemplateProgram.Data) (j : Fin 256)
    (hj : Protected j) : (embedState registers port d out).stacks j = d.stacks j := by
  apply embedState_stack_frame
  rintro ⟨i, he⟩
  exact port_ne_protected i j hj he

theorem template_output (d : Data) (out : SubexpTemplateProgram.Data) :
    (embedState registers port d out).stacks 200 = out.stacks 139 := by
  simpa only [port_output] using embedState_stack registers port d out port_injective 139

/-- Cache copies are discarded only after the actual template producer
returns, and before the job generator writes its stream on100. -/
theorem command_eval_from_trace (d : Data) (out : SubexpTemplateProgram.Data) (n : ℕ)
    (h : Trace SubexpTemplateProgram.program n
      ((localState d).withPC (some SubexpTemplateProgram.program.entry)) (out.withPC none)) :
    Eval command (n + SubexpNodeCacheSetup.cleanupCost (embedState registers port d out)) d
      (SubexpNodeCacheSetup.cleared SubexpNodeCacheSetup.cleanupPorts
        (embedState registers port d out)) :=
  (template_eval d out n h).seq (SubexpNodeCacheSetup.cleanup_eval _)

end SubexponentialSAT.SubexpNodeTemplateStage

end OAI.Algorithms
