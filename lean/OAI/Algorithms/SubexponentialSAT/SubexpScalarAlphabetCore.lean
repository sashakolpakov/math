import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ScalarSetupProgram
import OAI.Algorithms.SubexponentialSAT.CounterNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssembly
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

namespace OAI.Algorithms

/-! Fixed physical construction of the prime-field scalar cache. -/

namespace SubexponentialSAT.SubexpScalarAlphabetCore

open BitProgram StructuredCalls SubexpSetupStorage
open Subexp

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 16 14
abbrev Code := Cmd 16 14

def state (regs : Fin 16 → Bool) (source zero one modulus tokens raw frameZero frameOne : List Bool) : Data :=
  ⟨regs, ![source, zero, one, modulus, tokens, raw, frameZero, frameOne, [], [], [], [], [], []]⟩

def cleared : List (Fin 14) := (List.finRange 13).map Fin.succ

theorem mem_cleared (i : Fin 14) : i ∈ cleared ↔ i ≠ 0 := by
  simp only [cleared, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact Fin.succ_ne_zero j
  · intro hi
    exact ⟨i.pred hi, Fin.succ_pred i hi⟩

def normalizeRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def normalizePorts : Fin 3 → Fin 14 := ![1, 8, 9]
def scalarRegs : Fin 6 → Fin 16 := Fin.castAdd 10
def scalarPorts : Fin 9 → Fin 14 := ![1, 8, 9, 10, 11, 5, 4, 2, 3]
def framePorts (src : Fin 14) : Fin 3 → Fin 14 := ![src, 12, 13]

theorem normalizeRegs_injective : Function.Injective normalizeRegs := Fin.castAdd_injective _ _
theorem normalizePorts_injective : Function.Injective normalizePorts := by decide
theorem scalarRegs_injective : Function.Injective scalarRegs := Fin.castAdd_injective _ _
theorem scalarPorts_injective : Function.Injective scalarPorts := by decide

def normalize : Code := .call (ProgramLinking.liftProgram CounterNormalizeProgram.program
  normalizeRegs normalizePorts)
def scalar : Code := .call (ProgramLinking.liftProgram ScalarSetupProgram.program scalarRegs scalarPorts)
def frameCall (src : Fin 14) : Code :=
  .call (ProgramLinking.liftProgram SubexpBlockAssembly.frameBody normalizeRegs (framePorts src))
def frame (src dst : Fin 14) : Code :=
  .seq (.base (.atom (.set 2 true))) (.seq (frameCall src)
    (.call (StackRoutines.transferProgram 12 dst 0 1)))

def command : Code := .seq (clearMany cleared) (.seq (copyCmd 0 1 12)
  (.seq normalize (.seq scalar (.seq (frame 1 6) (.seq (frame 2 7) RegisterResetProgram.all)))))
abbrev program : Program 16 14 (size command + 1) := compiled command 0 4

def result (a : Data) (p : ℕ) [Fact p.Prime] : Data :=
  state (fun _ => false) (a.stacks 0) (MatrixWordEncoding.word p 0) (MatrixWordEncoding.word p 1)
    (MatrixWordEncoding.modulus p) (ProgramEncoding.encodeRecords (ScalarSetupProgram.tokenAlphabet p))
    (ProgramEncoding.encodeRecords (ScalarSetupProgram.rawAlphabet p))
    (Encoding.frame (MatrixWordEncoding.word p 0)) (Encoding.frame (MatrixWordEncoding.word p 1))

theorem clear_state (a : Data) : clearManyState cleared a =
    state (clearManyState cleared a).regs (a.stacks 0) [] [] [] [] [] [] [] := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  change (clearManyState cleared a).stacks i = _
  rw [clearMany_stacks]
  fin_cases i <;> simp [mem_cleared]

theorem copy_state (regs : Fin 16 → Bool) (bits : List Bool) :
    copyState 0 1 (state regs bits [] [] [] [] [] [] []) =
      state (readRegs regs 0 1 none) bits bits [] [] [] [] [] [] := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [state, StackRoutines.copyStacks]

theorem normalize_eval (regs : Fin 16 → Bool) (bits : List Bool) (p : ℕ)
    [Fact p.Prime] (hp : CounterPrograms.value bits = p) :
    ∃ ticks ≤ 9 * bits.length + 21, ∃ regs',
      Eval normalize ticks (state regs bits bits [] [] [] [] [] [])
        (state regs' bits (SubexpAlphabetProgram.primeWord p) [] [] [] [] [] []) := by
  let before := state regs bits bits [] [] [] [] [] []
  let localAfter := CounterNormalizeProgram.state CounterNormalizeProgram.zeroRegs
    (SubexpAlphabetProgram.primeWord p) []
  have hin : projectState normalizeRegs normalizePorts before =
      CounterNormalizeProgram.state (regs ∘ normalizeRegs) bits [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [before, state, normalizePorts]
  have hpos : 0 < CounterPrograms.value bits := by
    rw [hp]
    exact (Fact.out : p.Prime).pos
  have hcanon : SubexpLiftRing.fixedBits (Nat.log2 (CounterPrograms.value bits) + 1)
      (CounterPrograms.value bits) = SubexpAlphabetProgram.primeWord p := by
    rw [hp]
    simp only [SubexpAlphabetProgram.primeWord, SubexpEnumerationPayload.scalarWidth, Nat.log2_eq_log_two]
  obtain ⟨ticks, htime, ht⟩ := CounterNormalizeProgram.normalize_runs (regs ∘ normalizeRegs) bits hpos
  rw [hcanon] at ht
  let after := embedState normalizeRegs normalizePorts before localAfter
  have hout : after = state after.regs bits (SubexpAlphabetProgram.primeWord p) [] [] [] [] [] [] := by
    apply embedState_eq_of_ports normalizeRegs normalizePorts before _ localAfter
      normalizeRegs_injective normalizePorts_injective
    · exact fun i => embedState_register normalizeRegs normalizePorts before localAfter normalizeRegs_injective i
    · exact fun i hi => embedState_register_frame normalizeRegs normalizePorts before localAfter i hi
    · intro i
      fin_cases i <;> simp [state, normalizePorts, localAfter, CounterNormalizeProgram.state]
    · intro i hi
      fin_cases i <;> first | rfl | exact False.elim (hi ⟨0, rfl⟩)
  have he := eval_call_from_state CounterNormalizeProgram.program normalizeRegs normalizePorts before
    normalizeRegs_injective normalizePorts_injective (by simpa only [hin] using ht)
  exact ⟨ticks, htime, after.regs, by simpa only [normalize, ← hout] using he⟩

theorem scalar_eval (regs : Fin 16 → Bool) (bits : List Bool) (p : ℕ) [Fact p.Prime] :
    ∃ ticks ≤ ScalarSetupProgram.budget p, ∃ regs',
      Eval scalar ticks (state regs bits (SubexpAlphabetProgram.primeWord p) [] [] [] [] [] [])
        (state regs' bits (MatrixWordEncoding.word p 0) (MatrixWordEncoding.word p 1)
          (MatrixWordEncoding.modulus p) (ProgramEncoding.encodeRecords (ScalarSetupProgram.tokenAlphabet p))
          (ProgramEncoding.encodeRecords (ScalarSetupProgram.rawAlphabet p)) [] []) := by
  let before := state regs bits (SubexpAlphabetProgram.primeWord p) [] [] [] [] [] []
  have hin : projectState scalarRegs scalarPorts before = ScalarSetupProgram.inputState p (regs ∘ scalarRegs) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [before, state, scalarPorts]
  obtain ⟨localRegs, ticks, htime, ht⟩ := ScalarSetupProgram.program_run p (regs ∘ scalarRegs)
  let after := embedState scalarRegs scalarPorts before (ScalarSetupProgram.outputState p localRegs)
  have hout : after = state after.regs bits (MatrixWordEncoding.word p 0) (MatrixWordEncoding.word p 1)
      (MatrixWordEncoding.modulus p) (ProgramEncoding.encodeRecords (ScalarSetupProgram.tokenAlphabet p))
      (ProgramEncoding.encodeRecords (ScalarSetupProgram.rawAlphabet p)) [] [] := by
    apply embedState_eq_of_ports scalarRegs scalarPorts before _ (ScalarSetupProgram.outputState p localRegs)
      scalarRegs_injective scalarPorts_injective
    · exact fun i => embedState_register scalarRegs scalarPorts before
        (ScalarSetupProgram.outputState p localRegs) scalarRegs_injective i
    · exact fun i hi => embedState_register_frame scalarRegs scalarPorts before
        (ScalarSetupProgram.outputState p localRegs) i hi
    · intro i
      fin_cases i <;> simp [state, scalarPorts, ScalarSetupProgram.outputState, ScalarSetupProgram.state]
    · intro i hi
      fin_cases i <;> first | rfl | exact False.elim (hi ⟨0, rfl⟩) |
        exact False.elim (hi ⟨7, rfl⟩) | exact False.elim (hi ⟨8, rfl⟩) |
        exact False.elim (hi ⟨6, rfl⟩) | exact False.elim (hi ⟨5, rfl⟩)
  have he := eval_call_from_state ScalarSetupProgram.program scalarRegs scalarPorts before
    scalarRegs_injective scalarPorts_injective (by simpa only [hin] using ht)
  exact ⟨ticks, htime, after.regs, by simpa only [scalar, ← hout] using he⟩

theorem framePorts_injective (src : Fin 14) (h12 : src ≠ 12) (h13 : src ≠ 13) :
    Function.Injective (framePorts src) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [framePorts]

def backwards (a : Data) (src : Fin 14) : Data :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks 12 ((Encoding.frame (a.stacks src)).reverse)⟩

theorem frame_call_eval (a : Data) (src : Fin 14) (h12 : src ≠ 12) (h13 : src ≠ 13)
    (ha12 : a.stacks 12 = []) (ha13 : a.stacks 13 = []) (hreg : a.regs 2 = true) :
    Eval (frameCall src) (8 * (a.stacks src).length + 6) a (backwards a src) := by
  let before : State 3 3 := ⟨SubexpHornerProgram.triple (a.regs 0) (a.regs 1) true,
    SubexpHornerProgram.triple (a.stacks src) [] []⟩
  let after : State 3 3 := ⟨SubexpHornerProgram.triple false false true,
    SubexpHornerProgram.triple (a.stacks src) ((Encoding.frame (a.stacks src)).reverse) []⟩
  have hin : projectState normalizeRegs (framePorts src) a = before := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [normalizeRegs, SubexpHornerProgram.triple, hreg]
    · funext i
      fin_cases i <;> simp [framePorts, SubexpHornerProgram.triple, ha12, ha13]
  have hout : embedState normalizeRegs (framePorts src) a after = backwards a src := by
    apply embedState_eq_of_ports normalizeRegs (framePorts src) a _ after
      normalizeRegs_injective (framePorts_injective src h12 h13)
    · intro i
      fin_cases i <;> simp [backwards, after, normalizeRegs, SubexpHornerProgram.triple, readRegs, hreg]
    · intro i hi
      have h0 : i ≠ 0 := fun he => hi ⟨0, he.symm⟩
      have h1 : i ≠ 1 := fun he => hi ⟨1, he.symm⟩
      simp [backwards, readRegs, h0, h1]
    · intro i
      fin_cases i <;> simp [backwards, after, framePorts, SubexpHornerProgram.triple, h12, ha13]
    · intro i hi
      have h : i ≠ 12 := fun he => hi ⟨1, he.symm⟩
      simp [backwards, h]
  have ht : Trace SubexpBlockAssembly.frameBody (8 * (a.stacks src).length + 6)
      (before.withPC (some SubexpBlockAssembly.frameBody.entry)) (after.withPC none) := by
    simpa only [before, after, SubexpHornerProgram.Literal.cfg,
      StructuredProgram.State.withPC, List.append_nil] using
      SubexpBlockAssembly.frameBody_trace (a.stacks src) [] (a.regs 0) (a.regs 1)
  have he := eval_call_from_state SubexpBlockAssembly.frameBody normalizeRegs (framePorts src) a
    normalizeRegs_injective (framePorts_injective src h12 h13) (by simpa only [hin] using ht)
  simpa only [frameCall, hout] using he

theorem frame_eval (a : Data) (src dst : Fin 14) (h12 : src ≠ 12) (h13 : src ≠ 13)
    (hd12 : dst ≠ 12) (ha12 : a.stacks 12 = []) (ha13 : a.stacks 13 = []) (hd : a.stacks dst = []) :
    ∃ regs, Eval (frame src dst) (14 * (a.stacks src).length + 13) a
      ⟨regs, Function.update a.stacks dst (Encoding.frame (a.stacks src))⟩ := by
  let b : Data := ⟨Function.update a.regs 2 true, a.stacks⟩
  have hset : Eval (.base (.atom (.set 2 true))) 1 a b := .base (.atom _ _)
  have hf := frame_call_eval b src h12 h13 ha12 ha13 (by simp [b])
  let c := backwards b src
  let d : Data := ⟨readRegs c.regs 0 1 none, StackRoutines.transferStacks 12 dst c.stacks⟩
  have ht : Eval (.call (StackRoutines.transferProgram 12 dst 0 1))
      (3 * (c.stacks 12).length + 3) c d :=
    .call _ (ListRegisterProgram.transfer_run 12 dst 0 1 (Ne.symm hd12) (by decide) c.regs c.stacks)
  have hdstack : d.stacks = Function.update a.stacks dst (Encoding.frame (a.stacks src)) := by
    funext i
    by_cases hid : i = dst
    · subst i
      simp [d, c, b, backwards, StackRoutines.transferStacks, hd12, hd]
    · by_cases hi12 : i = 12
      · subst i
        simp [d, c, b, backwards, StackRoutines.transferStacks, hid, ha12]
      · simp [d, c, b, backwards, StackRoutines.transferStacks, hid, hi12]
  refine ⟨d.regs, ?_⟩
  have he := hset.seq (hf.seq ht)
  have hdEq : d = ⟨d.regs, Function.update a.stacks dst (Encoding.frame (a.stacks src))⟩ :=
    congrArg (StructuredProgram.State.mk d.regs) hdstack
  rw [hdEq] at he
  convert he using 1 <;> simp [frame, c, b, backwards, Encoding.length_frame]
  all_goals omega

def budget (a : Data) (p : ℕ) [Fact p.Prime] : ℕ :=
  clearManyCost cleared a + 16 * (a.stacks 0).length + ScalarSetupProgram.budget p +
    28 * MatrixWordEncoding.width p + 68

theorem command_eval (a : Data) (p : ℕ) [Fact p.Prime]
    (hp : CounterPrograms.value (a.stacks 0) = p) :
    ∃ ticks ≤ budget a p, Eval command ticks a (result a p) := by
  let bits := a.stacks 0
  let r0 := (clearManyState cleared a).regs
  let r1 := readRegs r0 0 1 none
  have hc := clearMany_eval cleared a
  rw [clear_state] at hc
  have hcopy := copy_eval 0 1 12 (state r0 bits [] [] [] [] [] [] [])
    (by decide) (by decide) (by decide) rfl
  rw [copy_state] at hcopy
  obtain ⟨tn, htn, rn, hn⟩ := normalize_eval r1 bits p hp
  obtain ⟨ts, hts, rs, hs⟩ := scalar_eval rn bits p
  let a4 := state rs bits (MatrixWordEncoding.word p 0) (MatrixWordEncoding.word p 1)
    (MatrixWordEncoding.modulus p) (ProgramEncoding.encodeRecords (ScalarSetupProgram.tokenAlphabet p))
    (ProgramEncoding.encodeRecords (ScalarSetupProgram.rawAlphabet p)) [] []
  obtain ⟨r5, hf0⟩ := frame_eval a4 1 6 (by decide) (by decide) (by decide) rfl rfl rfl
  let a5 := state r5 bits (MatrixWordEncoding.word p 0) (MatrixWordEncoding.word p 1)
    (MatrixWordEncoding.modulus p) (ProgramEncoding.encodeRecords (ScalarSetupProgram.tokenAlphabet p))
    (ProgramEncoding.encodeRecords (ScalarSetupProgram.rawAlphabet p))
    (Encoding.frame (MatrixWordEncoding.word p 0)) []
  have he5 : (⟨r5, Function.update a4.stacks 6 (Encoding.frame (a4.stacks 1))⟩ : Data) = a5 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [a4, state]
  rw [he5] at hf0
  obtain ⟨r6, hf1⟩ := frame_eval a5 2 7 (by decide) (by decide) (by decide) rfl rfl rfl
  let a6 := state r6 bits (MatrixWordEncoding.word p 0) (MatrixWordEncoding.word p 1)
    (MatrixWordEncoding.modulus p) (ProgramEncoding.encodeRecords (ScalarSetupProgram.tokenAlphabet p))
    (ProgramEncoding.encodeRecords (ScalarSetupProgram.rawAlphabet p))
    (Encoding.frame (MatrixWordEncoding.word p 0)) (Encoding.frame (MatrixWordEncoding.word p 1))
  have he6 : (⟨r6, Function.update a5.stacks 7 (Encoding.frame (a5.stacks 2))⟩ : Data) = a6 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [a5, state]
  rw [he6] at hf1
  have hr := RegisterResetProgram.all_eval a6
  change Eval RegisterResetProgram.all 16 a6 (result a p) at hr
  refine ⟨_, ?_, hc.seq (hcopy.seq (hn.seq (hs.seq (hf0.seq (hf1.seq hr)))))⟩
  simp only [bits] at htn
  simp [budget, a4, a5, state, bits]
  omega

theorem budget_le (a : Data) (p : ℕ) [Fact p.Prime] :
    budget a p + 1 ≤ 500 * (stackBits a.stacks + p + 1) * (MatrixWordEncoding.width p + 1) := by
  have hwords : WordBound (stackBits a.stacks) a := by
    intro i
    exact Finset.single_le_sum (fun (j : Fin 14) _ => Nat.zero_le (a.stacks j).length) (Finset.mem_univ i)
  have hc := clearManyCost_le cleared a (stackBits a.stacks) hwords
  have hlen : cleared.length = 13 := by simp [cleared]
  rw [hlen] at hc
  have hp := ScalarSetupProgram.budget_le p
  have h0 := hwords 0
  unfold budget
  nlinarith only [hc, hp, h0]

theorem program_run (a : Data) (p : ℕ) [Fact p.Prime]
    (hp : CounterPrograms.value (a.stacks 0) = p) :
    RunsIn program (budget a p + 1) (a.withPC (some program.entry)) ((result a p).withPC none) := by
  obtain ⟨ticks, ht, he⟩ := command_eval a p hp
  exact ⟨ticks + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 0 4⟩

end SubexponentialSAT.SubexpScalarAlphabetCore

end OAI.Algorithms
