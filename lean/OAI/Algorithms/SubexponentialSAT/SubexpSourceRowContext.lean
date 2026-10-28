import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupFrames
import OAI.Algorithms.SubexponentialSAT.CounterConversions
import OAI.Algorithms.SubexponentialSAT.SubexpJetInitProgram
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-!
# Physical initialization of the source-row evaluator

The source ring is read from stacks 128--130.  Read-only input 250 contains
the binary radius R and input 251 the target coefficient width.  A Main
adapter can map these two inputs directly to persistent slots 25 and 13.
The fixed program installs both arithmetic contexts, converts R to R+1
unary cells, and actually constructs the zero coefficient array.  The source
cache bank 128--137 is preserved.  Only stacks 246--249 are extra scratch.
-/

namespace SubexponentialSAT.SubexpSourceRowContext

open BitProgram StructuredCalls SubexpSetupStorage

abbrev Data := StructuredProgram.State 16 256
abbrev Command := Cmd 16 256

def radiusInput : Fin 256 := 250
def targetWidthInput : Fin 256 := 251
def copyTemporary : Fin 256 := 246
def binaryCopy : Fin 256 := 248
def unaryScratch : Fin 256 := 249

/-- These are exactly evaluator work regions; retained input and cache
regions, including the six arbitrary scalar frame words, are excluded. -/
def NeedsClear (i : Fin 256) : Prop :=
  i.val < 14 ∨ i = 21 ∨ (26 ≤ i.val ∧ i.val ≤ 29) ∨ i = 74 ∨ i = 87 ∨
  (99 ≤ i.val ∧ i.val ≤ 122) ∨ (138 ≤ i.val ∧ i.val ≤ 204) ∨
  (214 ≤ i.val ∧ i.val ≤ 223) ∨ (240 ≤ i.val ∧ i.val ≤ 249)

instance (i : Fin 256) : Decidable (NeedsClear i) := by
  unfold NeedsClear
  infer_instance

def clearPorts : List (Fin 256) :=
  (List.finRange 256).filter (fun i => decide (NeedsClear i))

@[simp] theorem mem_clearPorts (i : Fin 256) : i ∈ clearPorts ↔ NeedsClear i := by
  simp [clearPorts]

def copies : List (Fin 256 × Fin 256) :=
  [(128, 5), (128, 194), (129, 10), (129, 202), (130, 201),
    (targetWidthInput, 74), (radiusInput, binaryCopy)]

theorem copies_good : ∀ q ∈ copies,
    q.1 ≠ q.2 ∧ q.1 ≠ copyTemporary ∧ copyTemporary ≠ q.2 := by
  intro q hq
  simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem copies_separated : ∀ q ∈ copies, ∀ z ∈ copies, q.1 ≠ z.2 := by
  intro q hq z hz
  simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq hz
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem copies_nodup : (copies.map Prod.snd).Nodup := by decide

/-- Avoid expanding a universal decision over all pairs of physical ports. -/
theorem copies_avoid (i : Fin 256)
    (h : i ≠ 5 ∧ i ≠ 194 ∧ i ≠ 10 ∧ i ≠ 202 ∧ i ≠ 201 ∧ i ≠ 74 ∧ i ≠ binaryCopy) :
    ∀ q ∈ copies, i ≠ q.2 := by
  intro q hq
  simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

theorem copies_cleared : ∀ q ∈ copies, NeedsClear q.2 := by
  intro q hq
  simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem copies_inputs : ∀ q ∈ copies,
    ¬ NeedsClear q.1 ∧ q.1 ≠ copyTemporary := by
  intro q hq
  simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def prepared (a : Data) : Data := prepareState copyTemporary clearPorts copies a

theorem prepared_word (a : Data) (q : Fin 256 × Fin 256) (hq : q ∈ copies) :
    (prepared a).stacks q.2 = a.stacks q.1 := by
  have hz : ∀ z ∈ copies, (beforeCopies copyTemporary clearPorts a).stacks z.2 = [] := by
    intro z hz
    simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
      ite_eq_left ((mem_clearPorts _).mpr (copies_cleared z hz))]
  unfold prepared prepareState
  rw [copyMany_value copies _ copies_nodup hz copies_separated q hq]
  have hn : q.1 ∉ clearPorts := by simpa only [mem_clearPorts] using (copies_inputs q hq).1
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks, ite_eq_right hn]
  simp [(copies_inputs q hq).2]

theorem prepared_empty (a : Data) (i : Fin 256) (hi : NeedsClear i)
    (hd : ∀ q ∈ copies, i ≠ q.2) : (prepared a).stacks i = [] := by
  unfold prepared prepareState
  rw [copyMany_frame _ _ _ hd]
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
    ite_eq_left ((mem_clearPorts i).mpr hi)]

theorem prepared_frame (a : Data) (i : Fin 256) (hi : ¬ NeedsClear i) :
    (prepared a).stacks i = a.stacks i := by
  apply prepare_frame copyTemporary clearPorts copies a i
  · intro h
    subst i
    exact hi (by decide)
  · simpa only [mem_clearPorts] using hi
  · intro q hq h
    exact hi (h.symm ▸ copies_cleared q hq)

def dimension (a : Data) : ℕ := CounterPrograms.value (a.stacks radiusInput) + 1
def sourceWidth (a : Data) : ℕ := (a.stacks 129).length

def seed : Command :=
  .base (.seq (.atom (.set 0 true)) (.atom (.push 243 0)))

def seeded (a : Data) : Data :=
  ⟨Function.update (prepared a).regs 0 true,
    Function.update (prepared a).stacks 243 [true]⟩

theorem seed_eval (a : Data) : Eval seed 2 (prepared a) (seeded a) := by
  have h243 : (prepared a).stacks 243 = [] :=
    prepared_empty a 243 (by decide) (copies_avoid _ (by decide))
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 16) true) (prepared a)).seq
    (StructuredProgram.Eval.atom (.push (243 : Fin 256) 0) _)
  exact .base (by simpa [seeded, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, h243] using h)

def unaryRegister (i : Fin 3) : Fin 16 := i.castAdd 13
def unaryPort : Fin 3 → Fin 256 := ![binaryCopy, 243, unaryScratch]

theorem unaryRegister_injective : Function.Injective unaryRegister := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 16 => k.val) h)

theorem unaryPort_injective : Function.Injective unaryPort := by decide

def unaryOutput (a : Data) : CounterConversions.Data :=
  CounterConversions.state CounterConversions.zeroRegs [] (List.replicate (dimension a) true)

noncomputable def converted (a : Data) : Data :=
  embedState unaryRegister unaryPort (seeded a) (unaryOutput a)

theorem unary_entry (a : Data) :
    project unaryRegister unaryPort (seeded a) =
      CounterConversions.state ((seeded a).regs ∘ unaryRegister) (a.stacks radiusInput) [true] := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i
    · simpa [project, unaryPort, seeded, CounterConversions.state, binaryCopy] using
        prepared_word a (radiusInput, binaryCopy) (by simp [copies])
    · simp [unaryPort, seeded]
    · simpa [project, unaryPort, seeded, CounterConversions.state, unaryScratch] using
        prepared_empty a unaryScratch (by decide) (copies_avoid _ (by decide))

theorem converted_dimension (a : Data) :
    (converted a).stacks 243 = List.replicate (dimension a) true :=
  embedState_stack unaryRegister unaryPort (seeded a) (unaryOutput a)
    unaryPort_injective (1 : Fin 3)

theorem converted_binary (a : Data) : (converted a).stacks binaryCopy = [] :=
  embedState_stack unaryRegister unaryPort (seeded a) (unaryOutput a)
    unaryPort_injective (0 : Fin 3)

theorem converted_scratch (a : Data) : (converted a).stacks unaryScratch = [] :=
  embedState_stack unaryRegister unaryPort (seeded a) (unaryOutput a)
    unaryPort_injective (2 : Fin 3)

theorem converted_frame (a : Data) (i : Fin 256)
    (h0 : i ≠ binaryCopy) (h1 : i ≠ 243) (h2 : i ≠ unaryScratch) :
    (converted a).stacks i = (prepared a).stacks i := by
  have h := embedState_stack_frame unaryRegister unaryPort (seeded a) (unaryOutput a) i
    (by rintro ⟨j, hj⟩; fin_cases j
        · exact h0 hj.symm
        · exact h1 hj.symm
        · exact h2 hj.symm)
  exact h.trans (by simp [seeded, h1])

def jetPort (i : Fin 128) : Fin 256 :=
  if i = 102 then 242 else if i = 106 then 246 else if i = 107 then 247
  else if i = 108 then 248 else if i = 109 then 243 else i.castAdd 128

theorem jetPort_injective : Function.Injective jetPort := by
  intro i j h
  have hv := congrArg (fun k : Fin 256 => k.val) h
  have hi := i.isLt
  have hj := j.isLt
  simp only [jetPort] at hv
  split_ifs at hv <;> simp_all only [Fin.coe_ofNat_eq_mod, Fin.val_castAdd]
  all_goals omega

noncomputable def generated (a : Data) : Data :=
  embedState id jetPort (converted a)
    (SubexpJetInitProgram.initialized (project id jetPort (converted a))
      (dimension a) (sourceWidth a))

noncomputable def result (a : Data) : Data := RegisterResetProgram.zeroed (generated a)

theorem generated_stacks (a : Data) : (generated a).stacks =
    Function.update (Function.update (converted a).stacks 104
      (List.replicate (4 * sourceWidth a) false)) 242
      (List.replicate (dimension a * (4 * sourceWidth a)) false) := by
  have hbase : Function.extend jetPort ((converted a).stacks ∘ jetPort)
      (converted a).stacks = (converted a).stacks :=
    congrArg StructuredProgram.State.stacks
      (embed_project id jetPort Function.injective_id jetPort_injective (converted a))
  change Function.extend jetPort
    (Function.update (Function.update ((converted a).stacks ∘ jetPort) 104
      (List.replicate (4 * sourceWidth a) false)) 102
      (List.replicate (dimension a * (4 * sourceWidth a)) false))
    (converted a).stacks = _
  rw [ProgramLinking.extend_update jetPort_injective,
    ProgramLinking.extend_update jetPort_injective, hbase]
  rfl

theorem result_stacks (a : Data) : (result a).stacks = (generated a).stacks := rfl

@[simp] theorem result_dimension (a : Data) :
    (result a).stacks 243 = List.replicate (dimension a) true := by
  rw [result_stacks, generated_stacks]
  simpa using converted_dimension a

@[simp] theorem result_shape (a : Data) :
    (result a).stacks 104 = List.replicate (4 * sourceWidth a) false := by
  rw [result_stacks, generated_stacks]
  simp

@[simp] theorem result_zeroArray (a : Data) :
    (result a).stacks 242 = List.replicate (dimension a * (4 * sourceWidth a)) false := by
  rw [result_stacks, generated_stacks]
  simp

theorem result_prepared_frame (a : Data) (i : Fin 256)
    (h104 : i ≠ 104) (h242 : i ≠ 242) (h243 : i ≠ 243)
    (h248 : i ≠ binaryCopy) (h249 : i ≠ unaryScratch) :
    (result a).stacks i = (prepared a).stacks i := by
  rw [result_stacks, generated_stacks]
  simpa [h104, h242] using converted_frame a i h248 h243 h249

theorem result_word (a : Data) (q : Fin 256 × Fin 256) (hq : q ∈ copies)
    (hb : q.2 ≠ binaryCopy) : (result a).stacks q.2 = a.stacks q.1 := by
  have hs : q.2 ≠ (104 : Fin 256) ∧ q.2 ≠ 242 ∧ q.2 ≠ 243 ∧ q.2 ≠ unaryScratch := by
    simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [result_prepared_frame a q.2 hs.1 hs.2.1 hs.2.2.1 hb hs.2.2.2]
  exact prepared_word a q hq

theorem result_frame (a : Data) (i : Fin 256) (hi : ¬ NeedsClear i) :
    (result a).stacks i = a.stacks i := by
  have h104 : i ≠ (104 : Fin 256) := fun h => hi (h.symm ▸ (by decide))
  have h242 : i ≠ (242 : Fin 256) := fun h => hi (h.symm ▸ (by decide))
  have h243 : i ≠ (243 : Fin 256) := fun h => hi (h.symm ▸ (by decide))
  have h248 : i ≠ binaryCopy := fun h => hi (h.symm ▸ (by decide))
  have h249 : i ≠ unaryScratch := fun h => hi (h.symm ▸ (by decide))
  rw [result_prepared_frame a i h104 h242 h243 h248 h249]
  exact prepared_frame a i hi

theorem result_empty (a : Data) (i : Fin 256) (hi : NeedsClear i)
    (hd : ∀ q ∈ copies, i ≠ q.2) (h104 : i ≠ 104) (h242 : i ≠ 242)
    (h243 : i ≠ 243) : (result a).stacks i = [] := by
  rw [result_stacks, generated_stacks]
  simp only [Function.update_of_ne h104, Function.update_of_ne h242]
  by_cases hb : i = binaryCopy
  · subst i
    exact converted_binary a
  by_cases hs : i = unaryScratch
  · subst i
    exact converted_scratch a
  rw [converted_frame a i hb h243 hs]
  exact prepared_empty a i hi hd

theorem result_scratch_empty (a : Data) (i : Fin 256)
    (hlo : 246 ≤ i.val) (hhi : i.val ≤ 249) : (result a).stacks i = [] := by
  by_cases hb : i = binaryCopy
  · subst i
    rw [result_stacks, generated_stacks]
    simpa [binaryCopy] using converted_binary a
  apply result_empty a i
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, hhi⟩)))))))
  · intro q hq
    simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hb | intro h; have := congrArg Fin.val h; norm_num at this; omega
  all_goals intro h; have := congrArg Fin.val h; norm_num at this; omega

def command : Command :=
  .seq (prepare copyTemporary clearPorts copies)
    (.seq seed (.seq (invoke CounterConversions.unaryProgram unaryRegister unaryPort)
      (.seq (invoke SubexpJetInitProgram.program id jetPort) RegisterResetProgram.all)))

abbrev program : Program 16 256 (size command + 1) := compiled command radiusInput 242

def runtimeBound (a : Data) : ℕ :=
  prepareCost copyTemporary clearPorts copies a + 2 +
    CounterConversions.runtimeBound (a.stacks radiusInput) +
    (14 * sourceWidth a + dimension a * (28 * sourceWidth a + 14) + 18) + 17

theorem command_execution (a : Data) :
    ∃ n, Eval command n a (result a) ∧ n + 1 ≤ runtimeBound a := by
  obtain ⟨n, hn, ht⟩ := CounterConversions.unary_runs
    ((seeded a).regs ∘ unaryRegister) (a.stacks radiusInput) [true]
  have hcount : List.replicate (CounterPrograms.value (a.stacks radiusInput)) true ++ [true] =
      List.replicate (dimension a) true := by
    simpa only [dimension, List.replicate_one] using
      (List.replicate_add (CounterPrograms.value (a.stacks radiusInput)) 1 true).symm
  have hlocal : Trace CounterConversions.unaryProgram n
      ((project unaryRegister unaryPort (seeded a)).withPC
        (some CounterConversions.unaryProgram.entry)) ((unaryOutput a).withPC none) := by
    rw [unary_entry]
    simpa only [unaryOutput, hcount] using ht
  have hu := invoke_eval CounterConversions.unaryProgram unaryRegister unaryPort
    unaryRegister_injective unaryPort_injective (seeded a) (unaryOutput a) hlocal
  have hwidth : ((project id jetPort (converted a)).stacks 10).length = sourceWidth a := by
    change ((converted a).stacks 10).length = sourceWidth a
    rw [converted_frame a 10 (by decide) (by decide) (by decide)]
    exact congrArg List.length (prepared_word a (129, 10) (by simp [copies]))
  have hdim : (project id jetPort (converted a)).stacks 109 =
      List.replicate (dimension a) true := converted_dimension a
  have hempty : ∀ i ∈ ([102, 104, 106, 107, 108] : List (Fin 128)),
      (project id jetPort (converted a)).stacks i = [] := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · change (converted a).stacks 242 = []
      rw [converted_frame a 242 (by decide) (by decide) (by decide)]
      exact prepared_empty a 242 (by decide) (copies_avoid _ (by decide))
    · change (converted a).stacks 104 = []
      rw [converted_frame a 104 (by decide) (by decide) (by decide)]
      exact prepared_empty a 104 (by decide) (copies_avoid _ (by decide))
    · change (converted a).stacks 246 = []
      rw [converted_frame a 246 (by decide) (by decide) (by decide)]
      exact prepared_empty a 246 (by decide) (copies_avoid _ (by decide))
    · change (converted a).stacks 247 = []
      rw [converted_frame a 247 (by decide) (by decide) (by decide)]
      exact prepared_empty a 247 (by decide) (copies_avoid _ (by decide))
    · exact converted_binary a
  have hj := SubexpJetInitProgram.program_trace (project id jetPort (converted a))
    (dimension a) (sourceWidth a) hwidth hdim
    (hempty 102 (by simp)) (hempty 104 (by simp)) (hempty 106 (by simp))
    (hempty 107 (by simp)) (hempty 108 (by simp))
  have hg := invoke_eval SubexpJetInitProgram.program id jetPort Function.injective_id
    jetPort_injective (converted a) _ hj
  refine ⟨prepareCost copyTemporary clearPorts copies a +
    (2 + (n + ((14 * sourceWidth a + dimension a * (28 * sourceWidth a + 14) + 18) + 16))),
    .seq (prepare_eval copyTemporary clearPorts copies a copies_good)
      (.seq (seed_eval a) (.seq hu (.seq hg (RegisterResetProgram.all_eval _)))), ?_⟩
  unfold runtimeBound
  omega

theorem program_runs (a : Data) :
    RunsIn program (runtimeBound a)
      (a.withPC (some program.entry)) ((result a).withPC none) := by
  obtain ⟨n, hn, hb⟩ := command_execution a
  exact ⟨n + 1, hb, compiled_halt_trace hn radiusInput 242⟩

theorem result_registers (a : Data) (i : Fin 16) : (result a).regs i = false := rfl

theorem result_source (a : Data) (i : Fin 10) :
    (result a).stacks ⟨128 + i.val, by omega⟩ = a.stacks ⟨128 + i.val, by omega⟩ := by
  apply result_frame
  simp only [NeedsClear, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
  have := i.isLt
  omega

end SubexponentialSAT.SubexpSourceRowContext

end OAI.Algorithms
