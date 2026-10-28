import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupFrames
import OAI.Algorithms.SubexponentialSAT.CounterConversions
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-!
# Physical preparation of the CRT controller

The first 320 stacks use the CRT controller's local ABI. Seven retained input
words occupy 320..326: modulus, width, reduction, inverse exponent, quartic one,
scalar minus one, and binary D. Three additional stacks are copy/conversion
scratch. The node and jet arrays at 256 and 265 are preserved. Every other CRT
work stack is physically cleared before the context is copied and D converted.
-/

namespace SubexponentialSAT.SubexpCRTPreparation

open BitProgram StructuredCalls SubexpSetupStorage

abbrev Data := StructuredProgram.State 16 330
abbrev Command := Cmd 16 330

def inputPort (i : Fin 7) : Fin 330 := ⟨320 + i.val, by omega⟩
def copyTemporary : Fin 330 := 327
def binaryCopy : Fin 330 := 328
def unaryScratch : Fin 330 := 329

def NeedsClear (i : Fin 330) : Prop :=
  (i.val < 320 ∧ i ≠ 256 ∧ i ≠ 265) ∨ i = binaryCopy ∨ i = unaryScratch

instance (i : Fin 330) : Decidable (NeedsClear i) := by unfold NeedsClear; infer_instance

def clearPorts : List (Fin 330) :=
  (List.finRange 330).filter (fun i => decide (NeedsClear i))

@[simp] theorem mem_clearPorts (i : Fin 330) : i ∈ clearPorts ↔ NeedsClear i := by
  simp [clearPorts]

def copies : List (Fin 330 × Fin 330) :=
  [(320, 5), (320, 194), (321, 10), (321, 202), (322, 201),
    (323, 206), (324, 207), (325, 211), (326, 328)]

theorem copies_good : ∀ q ∈ copies,
    q.1 ≠ q.2 ∧ q.1 ≠ copyTemporary ∧ copyTemporary ≠ q.2 := by
  intro q hq
  simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem copies_separated : ∀ q ∈ copies, ∀ z ∈ copies, q.1 ≠ z.2 := by
  intro q hq z hz
  simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq hz
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem copies_nodup : (copies.map Prod.snd).Nodup := by decide

theorem copies_cleared : ∀ q ∈ copies, NeedsClear q.2 := by
  intro q hq
  simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem copies_input_range : ∀ q ∈ copies, 320 ≤ q.1.val ∧ q.1.val < 327 := by
  intro q hq
  simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem copies_avoid_unary : ∀ q ∈ copies, q.2 ≠ (243 : Fin 330) ∧ q.2 ≠ unaryScratch := by
  intro q hq
  simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem input_not_clear (i : Fin 7) : ¬ NeedsClear (inputPort i) := by
  simp only [NeedsClear, inputPort, binaryCopy, unaryScratch, Fin.ext_iff]
  omega

def prepared (a : Data) : Data := prepareState copyTemporary clearPorts copies a

theorem prepared_word (a : Data) (q : Fin 330 × Fin 330) (hq : q ∈ copies) :
    (prepared a).stacks q.2 = a.stacks q.1 := by
  have hz : ∀ z ∈ copies, (beforeCopies copyTemporary clearPorts a).stacks z.2 = [] := by
    intro z hz
    simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
      ite_eq_left ((mem_clearPorts _).mpr (copies_cleared z hz))]
  unfold prepared prepareState
  rw [copyMany_value copies _ copies_nodup hz copies_separated q hq]
  have hr := copies_input_range q hq
  have hn : q.1 ∉ clearPorts := by
    rw [mem_clearPorts]
    simp only [NeedsClear, binaryCopy, unaryScratch, Fin.ext_iff]
    omega
  have ht : q.1 ≠ copyTemporary := by
    intro he
    have hv := congrArg Fin.val he
    change q.1.val = 327 at hv
    omega
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks, ite_eq_right hn]
  simp [ht]

theorem prepared_empty (a : Data) (i : Fin 330) (hi : NeedsClear i)
    (hd : ∀ q ∈ copies, i ≠ q.2) : (prepared a).stacks i = [] := by
  unfold prepared prepareState
  rw [copyMany_frame _ _ _ hd]
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
    ite_eq_left ((mem_clearPorts i).mpr hi)]

theorem prepared_frame (a : Data) (i : Fin 330) (hi : ¬ NeedsClear i)
    (ht : i ≠ copyTemporary) : (prepared a).stacks i = a.stacks i := by
  apply prepare_frame copyTemporary clearPorts copies a i ht
  · simpa only [mem_clearPorts] using hi
  · intro q hq he
    exact hi (he.symm ▸ copies_cleared q hq)

def unaryRegister (i : Fin 3) : Fin 16 := i.castAdd 13
def unaryPort : Fin 3 → Fin 330 := ![binaryCopy, 243, unaryScratch]

theorem unaryRegister_injective : Function.Injective unaryRegister := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 16 => k.val) h)

theorem unaryPort_injective : Function.Injective unaryPort := by decide

def unaryOutput (a : Data) : CounterConversions.Data :=
  CounterConversions.state CounterConversions.zeroRegs []
    (List.replicate (CounterPrograms.value (a.stacks 326)) true)

noncomputable def converted (a : Data) : Data :=
  embedState unaryRegister unaryPort (prepared a) (unaryOutput a)

noncomputable def result (a : Data) : Data := RegisterResetProgram.zeroed (converted a)

def command : Command :=
  .seq (prepare copyTemporary clearPorts copies)
    (.seq (invoke CounterConversions.unaryProgram unaryRegister unaryPort)
      RegisterResetProgram.all)

abbrev program : Program 16 330 (size command + 1) := compiled command 256 243

def runtimeBound (a : Data) : ℕ :=
  prepareCost copyTemporary clearPorts copies a +
    CounterConversions.runtimeBound (a.stacks 326) + 17

theorem unary_entry (a : Data) :
    project unaryRegister unaryPort (prepared a) =
      CounterConversions.state ((prepared a).regs ∘ unaryRegister) (a.stacks 326) [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i
    · exact prepared_word a (326, 328) (by simp [copies])
    · exact prepared_empty a 243 (by decide)
        (fun q hq => (copies_avoid_unary q hq).1.symm)
    · exact prepared_empty a 329 (by decide)
        (fun q hq => (copies_avoid_unary q hq).2.symm)

theorem command_execution (a : Data) :
    ∃ n, Eval command n a (result a) ∧ n + 1 ≤ runtimeBound a := by
  obtain ⟨n, hn, ht⟩ := CounterConversions.unary_runs
    ((prepared a).regs ∘ unaryRegister) (a.stacks 326) []
  have hlocal : Trace CounterConversions.unaryProgram n
      ((project unaryRegister unaryPort (prepared a)).withPC
        (some CounterConversions.unaryProgram.entry)) ((unaryOutput a).withPC none) := by
    rw [unary_entry]
    simpa only [unaryOutput, List.append_nil] using ht
  have hc := invoke_eval CounterConversions.unaryProgram unaryRegister unaryPort
    unaryRegister_injective unaryPort_injective (prepared a) (unaryOutput a) hlocal
  refine ⟨prepareCost copyTemporary clearPorts copies a + (n + 16),
    .seq (prepare_eval copyTemporary clearPorts copies a copies_good)
      (.seq hc (RegisterResetProgram.all_eval _)), ?_⟩
  unfold runtimeBound
  omega

theorem program_runs (a : Data) :
    RunsIn program (runtimeBound a)
      (a.withPC (some program.entry)) ((result a).withPC none) := by
  obtain ⟨n, hn, hb⟩ := command_execution a
  exact ⟨n + 1, hb, compiled_halt_trace hn 256 243⟩

theorem result_registers (a : Data) (i : Fin 16) : (result a).regs i = false := rfl

theorem result_unary (a : Data) : (result a).stacks 243 =
    List.replicate (CounterPrograms.value (a.stacks 326)) true :=
  embedState_stack unaryRegister unaryPort (prepared a) (unaryOutput a)
    unaryPort_injective (1 : Fin 3)

theorem result_binary (a : Data) : (result a).stacks binaryCopy = [] :=
  embedState_stack unaryRegister unaryPort (prepared a) (unaryOutput a)
    unaryPort_injective (0 : Fin 3)

theorem result_unaryScratch (a : Data) : (result a).stacks unaryScratch = [] :=
  embedState_stack unaryRegister unaryPort (prepared a) (unaryOutput a)
    unaryPort_injective (2 : Fin 3)

theorem result_prepared_frame (a : Data) (i : Fin 330)
    (h0 : i ≠ binaryCopy) (h1 : i ≠ 243) (h2 : i ≠ unaryScratch) :
    (result a).stacks i = (prepared a).stacks i := by
  apply embedState_stack_frame unaryRegister unaryPort (prepared a) (unaryOutput a) i
  rintro ⟨j, hj⟩
  fin_cases j
  · exact h0 hj.symm
  · exact h1 hj.symm
  · exact h2 hj.symm

theorem result_word (a : Data) (q : Fin 330 × Fin 330) (hq : q ∈ copies)
    (hb : q.2 ≠ binaryCopy) : (result a).stacks q.2 = a.stacks q.1 := by
  rw [result_prepared_frame a q.2 hb (copies_avoid_unary q hq).1 (copies_avoid_unary q hq).2]
  exact prepared_word a q hq

theorem result_empty (a : Data) (i : Fin 330) (hi : NeedsClear i)
    (hd : ∀ q ∈ copies, i ≠ q.2) (hu : i ≠ 243) : (result a).stacks i = [] := by
  by_cases hb : i = binaryCopy
  · subst i; exact result_binary a
  by_cases hs : i = unaryScratch
  · subst i; exact result_unaryScratch a
  rw [result_prepared_frame a i hb hu hs]
  exact prepared_empty a i hi hd

theorem result_copyTemporary (a : Data) : (result a).stacks copyTemporary = [] := by
  rw [result_prepared_frame a copyTemporary (by decide) (by decide) (by decide)]
  exact prepare_temporary copyTemporary clearPorts copies a copies_good

theorem result_input (a : Data) (i : Fin 7) :
    (result a).stacks (inputPort i) = a.stacks (inputPort i) := by
  have hv := i.isLt
  have h0 : inputPort i ≠ binaryCopy := by
    simp [inputPort, binaryCopy, Fin.ext_iff]
    omega
  have h1 : inputPort i ≠ (243 : Fin 330) := by
    simp [inputPort, Fin.ext_iff]
    omega
  have h2 : inputPort i ≠ unaryScratch := by
    simp [inputPort, unaryScratch, Fin.ext_iff]
    omega
  rw [result_prepared_frame a _ h0 h1 h2]
  apply prepared_frame a _ (input_not_clear i)
  simp [inputPort, copyTemporary, Fin.ext_iff]
  omega

theorem result_nodes (a : Data) : (result a).stacks 256 = a.stacks 256 := by
  rw [result_prepared_frame a 256 (by decide) (by decide) (by decide)]
  exact prepared_frame a 256 (by decide) (by decide)

theorem result_jets (a : Data) : (result a).stacks 265 = a.stacks 265 := by
  rw [result_prepared_frame a 265 (by decide) (by decide) (by decide)]
  exact prepared_frame a 265 (by decide) (by decide)

end SubexponentialSAT.SubexpCRTPreparation

end OAI.Algorithms
