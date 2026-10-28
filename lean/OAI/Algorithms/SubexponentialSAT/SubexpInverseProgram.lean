import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticMachine
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpResidueInverse

namespace OAI.Algorithms

/-!
# A binary-counted geometric inverse controller

The program uses a fixed 71-word bank, the scalar workspace, and two binary
counter stacks. It caches b, forms z = 1 - a*b, starts the accumulator at zero,
performs the supplied number of Horner steps, and multiplies the result by b.
Prepared words for one, minus one, and zero remain explicit input data.
-/

namespace SubexponentialSAT.SubexpInverseProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.SubexpQuarticMachine
open SubexponentialSAT.StructuredProgram

private theorem quad_ext {A : Type*} {a b : Quad A}
    (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) (h2 : a.c2 = b.c2) (h3 : a.c3 = b.c3) :
    a = b := by
  cases a
  cases b
  simp_all

def widenInstruction (i : SubexponentialSAT.SubexpQuarticMachine.Instr 61) :
    SubexponentialSAT.SubexpQuarticMachine.Instr 71 :=
  ⟨i.op, Fin.castAdd 10 i.dst, Fin.castAdd 10 i.lhs, Fin.castAdd 10 i.rhs⟩

def multiplyCode : List (SubexponentialSAT.SubexpQuarticMachine.Instr 71) :=
  mulCode.map widenInstruction

def cacheCode : List (SubexponentialSAT.SubexpQuarticMachine.Instr 71) :=
  [⟨.add, 61, 8, 70⟩, ⟨.add, 62, 9, 70⟩,
   ⟨.add, 63, 10, 70⟩, ⟨.add, 64, 11, 70⟩]

def negateCode : List (SubexponentialSAT.SubexpQuarticMachine.Instr 71) :=
  [⟨.mul, 4, 57, 69⟩, ⟨.mul, 5, 58, 69⟩,
   ⟨.mul, 6, 59, 69⟩, ⟨.mul, 7, 60, 69⟩]

def defectCode : List (SubexponentialSAT.SubexpQuarticMachine.Instr 71) :=
  [⟨.add, 4, 4, 65⟩, ⟨.add, 5, 5, 66⟩,
   ⟨.add, 6, 6, 67⟩, ⟨.add, 7, 7, 68⟩]

def zeroCode : List (SubexponentialSAT.SubexpQuarticMachine.Instr 71) :=
  [⟨.add, 8, 70, 70⟩, ⟨.add, 9, 70, 70⟩,
   ⟨.add, 10, 70, 70⟩, ⟨.add, 11, 70, 70⟩]

def accumulateCode : List (SubexponentialSAT.SubexpQuarticMachine.Instr 71) :=
  [⟨.add, 8, 57, 65⟩, ⟨.add, 9, 58, 66⟩,
   ⟨.add, 10, 59, 67⟩, ⟨.add, 11, 60, 68⟩]

def restoreCode : List (SubexponentialSAT.SubexpQuarticMachine.Instr 71) :=
  [⟨.add, 4, 61, 70⟩, ⟨.add, 5, 62, 70⟩,
   ⟨.add, 6, 63, 70⟩, ⟨.add, 7, 64, 70⟩]

def initializeCode := cacheCode ++ multiplyCode ++ negateCode ++ defectCode ++ zeroCode
def bodyCode := multiplyCode ++ accumulateCode
def finishCode := restoreCode ++ multiplyCode

theorem initializeCode_length : initializeCode.length = 65 := rfl
theorem bodyCode_length : bodyCode.length = 53 := rfl
theorem finishCode_length : finishCode.length = 53 := rfl

abbrev Bank (B : ℕ) := Fin 71 → Word B
abbrev Data := StructuredCalls.State 8 82

def lowerPorts : Fin 80 → Fin 82 := Fin.castAdd 2

theorem lowerPorts_injective : Function.Injective lowerPorts := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 82 => x.val) h)

def counterPorts : CounterForPrograms.Ports 8 82 where
  register := ⟨Fin.castAdd 5, by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)⟩
  counter := 80
  scratch := 81
  counter_ne_scratch := by decide

def extendedStacks {B : ℕ} (bank : Bank B) (modulus counter scratch : List Bool) :
    Fin 82 → List Bool :=
  fun j => Fin.addCases (m := 80) (n := 2) (motive := fun _ => List Bool)
    (restingState (fun _ => false) bank modulus).stacks
    (fun i : Fin 2 => if i = 0 then counter else scratch) j

def extendedState {B : ℕ} (regs : Fin 8 → Bool) (bank : Bank B)
    (modulus counter scratch : List Bool) : Data :=
  ⟨regs, extendedStacks bank modulus counter scratch⟩

@[simp] theorem extendedStacks_lower {B : ℕ} (bank : Bank B)
    (modulus counter scratch : List Bool) (j : Fin 80) :
    extendedStacks bank modulus counter scratch (lowerPorts j) =
      (restingState (fun _ => false) bank modulus).stacks j := by
  simp [extendedStacks, lowerPorts]

@[simp] theorem extendedStacks_counter {B : ℕ} (bank : Bank B)
    (modulus counter scratch : List Bool) :
    extendedStacks bank modulus counter scratch 80 = counter := rfl

@[simp] theorem extendedStacks_scratch {B : ℕ} (bank : Bank B)
    (modulus counter scratch : List Bool) :
    extendedStacks bank modulus counter scratch 81 = scratch := rfl

private theorem state_ext {a b : Data} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by cases a; cases b; simp_all

theorem extendedState_of_lower {B : ℕ} (d : Data) (bank : Bank B) (modulus : List Bool)
    (h : ∀ j, d.stacks (lowerPorts j) =
      (restingState (fun _ => false) bank modulus).stacks j) :
    d = extendedState d.regs bank modulus (d.stacks 80) (d.stacks 81) := by
  apply state_ext
  · rfl
  · funext j
    by_cases hj : j.val < 80
    · let i : Fin 80 := ⟨j.val, hj⟩
      have he : lowerPorts i = j := Fin.ext rfl
      rw [← he]
      exact (h i).trans (extendedStacks_lower bank modulus _ _ i).symm
    · have hv : j.val = 80 ∨ j.val = 81 := by omega
      rcases hv with hv | hv
      · have he : j = 80 := Fin.ext hv
        subst j
        rfl
      · have he : j = 81 := Fin.ext hv
        subst j
        rfl

private theorem embed_lower {B : ℕ} (regs frameRegs : Fin 8 → Bool) (bank frameBank : Bank B)
    (modulus counter scratch : List Bool) :
    StructuredCalls.embedState id lowerPorts
      (extendedState frameRegs frameBank modulus counter scratch)
      (restingState regs bank modulus) = extendedState regs bank modulus counter scratch := by
  apply state_ext
  · simp [StructuredCalls.embedState, extendedState, restingState]
  · funext j
    by_cases hj : j.val < 80
    · let i : Fin 80 := ⟨j.val, hj⟩
      have he : lowerPorts i = j := Fin.ext rfl
      rw [← he]
      exact (StructuredCalls.embedState_stack id lowerPorts
        (extendedState frameRegs frameBank modulus counter scratch)
        (restingState regs bank modulus) lowerPorts_injective i).trans
        (extendedStacks_lower bank modulus counter scratch i).symm
    · have hv : j.val = 80 ∨ j.val = 81 := by omega
      rcases hv with hv | hv
      · have he : j = 80 := Fin.ext hv
        subst j
        exact StructuredCalls.embedState_stack_frame id lowerPorts _ _ 80 (by
          rintro ⟨i, hi⟩
          have := congrArg (fun x : Fin 82 => x.val) hi
          simp [lowerPorts] at this
          omega)
      · have he : j = 81 := Fin.ext hv
        subst j
        exact StructuredCalls.embedState_stack_frame id lowerPorts _ _ 81 (by
          rintro ⟨i, hi⟩
          have := congrArg (fun x : Fin 82 => x.val) hi
          simp [lowerPorts] at this
          omega)

def lowerProgram (code : List (SubexponentialSAT.SubexpQuarticMachine.Instr 71)) :=
  StructuredCalls.compiled (scriptCmd code) (bankPort 4) (bankPort 57)

abbrev codeCommand (code : List (SubexponentialSAT.SubexpQuarticMachine.Instr 71)) : StructuredCalls.Cmd 8 82 :=
  .call (liftProgram (lowerProgram code) id lowerPorts)

theorem codeCommand_eval (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ)
    (code : List (SubexponentialSAT.SubexpQuarticMachine.Instr 71)) (regs : Fin 8 → Bool)
    (bank : Bank (baseWidth p μ)) (counter : List Bool) :
    ∃ n finalRegs, n ≤ code.length * 6100 * (baseWidth p μ + 1)^2 + 1 ∧
      StructuredCalls.Eval (codeCommand code) n
        (extendedState regs bank M.bits counter [])
        (extendedState finalRegs (scriptEval p μ M code bank) M.bits counter []) := by
  obtain ⟨n, rf, hn, he⟩ := script_run p μ M code regs bank
  have ht := StructuredCalls.compiled_halt_trace he (bankPort 4) (bankPort 57)
  have hw := StructuredCalls.eval_call_lifted (lowerProgram code) id lowerPorts
    (extendedState regs bank M.bits counter []) Function.injective_id lowerPorts_injective ht
  rw [embed_lower, embed_lower] at hw
  exact ⟨n + 1, rf, Nat.add_le_add_right hn 1, hw⟩

abbrev inverseCommand : StructuredCalls.Cmd 8 82 :=
  .seq (codeCommand initializeCode)
    (.seq (CounterForPrograms.forCmd counterPorts (codeCommand bodyCode)) (codeCommand finishCode))

def inverseProgram := StructuredCalls.compiled inverseCommand 4 57

def runBank (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (iterations : ℕ) (bank : Bank (baseWidth p μ)) : Bank (baseWidth p μ) :=
  scriptEval p μ M finishCode
    ((scriptEval p μ M bodyCode)^[iterations] (scriptEval p μ M initializeCode bank))

def instructionBound (B C iterations : ℕ) : ℕ :=
  (65 * 6100 * (B + 1)^2 + 1) +
    (iterations * (53 * 6100 * (B + 1)^2 + 1) +
      (iterations + 1) * (16 * C + 16)) +
    (53 * 6100 * (B + 1)^2 + 1) + 1

private theorem lower_ne_counter (j : Fin 80) : lowerPorts j ≠ counterPorts.counter := by
  intro h
  have := congrArg Fin.val h
  simp [lowerPorts, counterPorts] at this
  omega

private theorem lower_ne_scratch (j : Fin 80) : lowerPorts j ≠ counterPorts.scratch := by
  intro h
  have := congrArg Fin.val h
  simp [lowerPorts, counterPorts] at this
  omega

def loopInvariant (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (initialBank : Bank (baseWidth p μ)) (i : ℕ) (d : Data) : Prop :=
  ∀ j : Fin 80, d.stacks (lowerPorts j) =
    (restingState (fun _ => false)
      ((scriptEval p μ M bodyCode)^[i] initialBank) M.bits).stacks j

theorem loopInvariant_stable (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (bank : Bank (baseWidth p μ)) :
    CounterForPrograms.FrameStable counterPorts (loopInvariant p μ M bank) := by
  intro i d e heq hi j
  exact (heq (lowerPorts j) (lower_ne_counter j) (lower_ne_scratch j)).symm.trans (hi j)

theorem body_spec (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (bank : Bank (baseWidth p μ)) :
    CounterForPrograms.BodySpec counterPorts (codeCommand bodyCode)
      (loopInvariant p μ M bank)
      (fun _ => 53 * 6100 * (baseWidth p μ + 1)^2 + 1) := by
  intro i d hi hs _
  let bi := (scriptEval p μ M bodyCode)^[i] bank
  have hd : d = extendedState d.regs bi M.bits (d.stacks 80) [] := by
    calc
      d = extendedState d.regs bi M.bits (d.stacks 80) (d.stacks 81) :=
        extendedState_of_lower d bi M.bits hi
      _ = extendedState d.regs bi M.bits (d.stacks 80) [] := by
        rw [show d.stacks 81 = [] from hs]
  obtain ⟨n, rf, hn, he⟩ := codeCommand_eval p μ M bodyCode d.regs bi (d.stacks 80)
  rw [← hd] at he
  refine ⟨n, extendedState rf (scriptEval p μ M bodyCode bi) M.bits (d.stacks 80) [],
    ?_, he, rfl, rfl, ?_⟩
  · simpa only [bodyCode_length] using hn
  · intro j
    change extendedStacks (scriptEval p μ M bodyCode bi) M.bits (d.stacks 80) [] (lowerPorts j) = _
    rw [extendedStacks_lower]
    simp only [Function.iterate_succ_apply', bi]

/-- Actual instruction trace of the finite bank controller. The natural
iteration count in its specification is decoded only by the proof. -/
theorem inverse_execute (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (regs : Fin 8 → Bool)
    (bank : Bank (baseWidth p μ)) (counter : List Bool) :
    ∃ finalRegs finalCounter,
      RunsIn inverseProgram
        (instructionBound (baseWidth p μ) counter.length (CounterPrograms.value counter))
        ((extendedState regs bank M.bits counter []).withPC (some inverseProgram.entry))
        ((extendedState finalRegs (runBank p μ M (CounterPrograms.value counter) bank)
          M.bits finalCounter []).withPC none) ∧
      CounterPrograms.value finalCounter = 0 ∧ finalCounter.length = counter.length := by
  obtain ⟨ni, ri, hni, hei⟩ := codeCommand_eval p μ M initializeCode regs bank counter
  let initialized := scriptEval p μ M initializeCode bank
  have hi : loopInvariant p μ M initialized 0 (extendedState ri initialized M.bits counter []) := by
    intro j
    exact extendedStacks_lower initialized M.bits counter [] j
  obtain ⟨nl, e, hel, hie, hzero, hwidth, hscratch, hnl⟩ := CounterForPrograms.for_correct
    counterPorts (codeCommand bodyCode) (loopInvariant p μ M initialized)
    (fun _ => 53 * 6100 * (baseWidth p μ + 1)^2 + 1)
    (loopInvariant_stable p μ M initialized) (body_spec p μ M initialized)
    (extendedState ri initialized M.bits counter []) rfl hi
  let iterated := (scriptEval p μ M bodyCode)^[CounterPrograms.value counter] initialized
  have heq : e = extendedState e.regs iterated M.bits (e.stacks 80) [] := by
    calc
      e = extendedState e.regs iterated M.bits (e.stacks 80) (e.stacks 81) :=
        extendedState_of_lower e iterated M.bits hie
      _ = extendedState e.regs iterated M.bits (e.stacks 80) [] := by
        rw [show e.stacks 81 = [] from hscratch]
  obtain ⟨nf, rf, hnf, hef⟩ := codeCommand_eval p μ M finishCode e.regs iterated (e.stacks 80)
  rw [← heq] at hef
  have hall := StructuredCalls.Eval.seq hei (StructuredCalls.Eval.seq hel hef)
  have htrace := StructuredCalls.compiled_halt_trace hall (4 : Fin 82) 57
  refine ⟨rf, e.stacks 80, ⟨ni + (nl + nf) + 1, ?_, htrace⟩, hzero, hwidth⟩
  have hnl' : nl ≤ CounterPrograms.value counter *
      (53 * 6100 * (baseWidth p μ + 1)^2 + 1) +
      (CounterPrograms.value counter + 1) * (16 * counter.length + 16) := by
    simpa only [CounterForPrograms.budgetSum_const, counterPorts,
      extendedState, extendedStacks_counter] using hnl
  rw [initializeCode_length] at hni
  rw [finishCode_length] at hnf
  unfold instructionBound
  omega

theorem inverse_primitive (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (regs : Fin 8 → Bool)
    (bank : Bank (baseWidth p μ)) (counter : List Bool) :
    ∃ finalRegs finalCounter,
      Computation.RunsIn (primitive inverseProgram).step
        (primitiveOverhead inverseProgram *
          instructionBound (baseWidth p μ) counter.length (CounterPrograms.value counter))
        (primitiveCfg inverseProgram
          ((extendedState regs bank M.bits counter []).withPC (some inverseProgram.entry)))
        (primitiveCfg inverseProgram
          ((extendedState finalRegs (runBank p μ M (CounterPrograms.value counter) bank)
            M.bits finalCounter []).withPC none)) ∧
      CounterPrograms.value finalCounter = 0 ∧ finalCounter.length = counter.length := by
  obtain ⟨rf, counter', ht, hz, hl⟩ := inverse_execute p μ M regs bank counter
  exact ⟨rf, counter', BitProgram.primitive_execution _ ht, hz, hl⟩

/-! ## Algebraic interpretation of the concrete bank operations -/

def lowerBank {A : Type*} (bank : Fin 71 → A) : Fin 61 → A := fun i => bank (Fin.castAdd 10 i)

def reduction {A : Type*} (bank : Fin 71 → A) : Quad A := mulReduction (lowerBank bank)
def left {A : Type*} (bank : Fin 71 → A) : Quad A := mulLeft (lowerBank bank)
def right {A : Type*} (bank : Fin 71 → A) : Quad A := mulRight (lowerBank bank)
def output {A : Type*} (bank : Fin 71 → A) : Quad A := mulOutput (lowerBank bank)
def cached {A : Type*} (bank : Fin 71 → A) : Quad A := ⟨bank 61, bank 62, bank 63, bank 64⟩
def unit {A : Type*} (bank : Fin 71 → A) : Quad A := ⟨bank 65, bank 66, bank 67, bank 68⟩

theorem lowerBank_eval (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (i : SubexponentialSAT.SubexpQuarticMachine.Instr 61)
    (bank : Bank (baseWidth p μ)) :
    lowerBank ((widenInstruction i).eval p μ M bank) = i.eval p μ M (lowerBank bank) := by
  funext j
  by_cases hj : j = i.dst
  · subst j
    simp [lowerBank, Instr.eval, widenInstruction]
  · have hc : Fin.castAdd 10 j ≠ Fin.castAdd 10 i.dst :=
      fun h => hj ((Fin.castAdd_injective 61 10) h)
    simp [lowerBank, Instr.eval, widenInstruction, hj, hc]

theorem lowerBank_script (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (code : List (SubexponentialSAT.SubexpQuarticMachine.Instr 61))
    (bank : Bank (baseWidth p μ)) :
    lowerBank (scriptEval p μ M (code.map widenInstruction) bank) =
      scriptEval p μ M code (lowerBank bank) := by
  induction code generalizing bank with
  | nil => rfl
  | cons i code ih =>
    simp only [List.map_cons, scriptEval, ih, lowerBank_eval]

theorem multiplyCode_output (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (bank : Bank (baseWidth p μ)) :
    output (scriptEval p μ M multiplyCode bank) =
      (SubexpPreparedQuartic.binaryMul p μ M (reduction bank) (left bank) (right bank)).1 := by
  rw [output, multiplyCode, lowerBank_script]
  exact mulCode_correct p μ M (lowerBank bank)

theorem scriptEval_append (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ)
    (a b : List (SubexponentialSAT.SubexpQuarticMachine.Instr 71)) (bank : Bank (baseWidth p μ)) :
    scriptEval p μ M (a ++ b) bank = scriptEval p μ M b (scriptEval p μ M a bank) := by
  induction a generalizing bank with
  | nil => rfl
  | cons i a ih => simpa only [List.cons_append, scriptEval] using ih (i.eval p μ M bank)

theorem multiplyCode_frame (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (bank : Bank (baseWidth p μ))
    (j : Fin 71) (hj : j.val < 12 ∨ 61 ≤ j.val) :
    scriptEval p μ M multiplyCode bank j = bank j := by
  apply scriptEval_frame
  have hd : ∀ i ∈ multiplyCode, 12 ≤ i.dst.val ∧ i.dst.val < 61 := by
    decide
  intro i hi he
  have hh := hd i hi
  rw [he] at hh
  omega

theorem persistent_frame (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ)
    (code : List (SubexponentialSAT.SubexpQuarticMachine.Instr 71))
    (hd : ∀ i ∈ code, 4 ≤ i.dst.val ∧ i.dst.val < 65)
    (bank : Bank (baseWidth p μ)) (j : Fin 71) (hj : j.val < 4 ∨ 65 ≤ j.val) :
    scriptEval p μ M code bank j = bank j := by
  apply scriptEval_frame
  intro i hi he
  have hh := hd i hi
  rw [he] at hh
  omega

theorem iterate_persistent_frame (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (n : ℕ)
    (bank : Bank (baseWidth p μ)) (j : Fin 71) (hj : j.val < 4 ∨ 65 ≤ j.val) :
    ((scriptEval p μ M bodyCode)^[n] bank) j = bank j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', persistent_frame p μ M bodyCode (by decide) _ j hj, ih]

/-- Reduction coefficients and all prepared constants survive the complete call. -/
theorem runBank_frame (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (n : ℕ)
    (bank : Bank (baseWidth p μ)) (j : Fin 71) (hj : j.val < 4 ∨ 65 ≤ j.val) :
    runBank p μ M n bank j = bank j := by
  rw [runBank, persistent_frame p μ M finishCode (by decide) _ j hj,
    iterate_persistent_frame p μ M n _ j hj,
    persistent_frame p μ M initializeCode (by decide) bank j hj]

section Semantics

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
variable (c : Fin 4 → ZMod (p^μ))

noncomputable def denoteQuad (q : Quad (Word (baseWidth p μ))) :
    LiftRing.Extension (QuarticSearch.poly c) := quotientDenote c (q.map (wordValue p μ))

def Constants (bank : Bank (baseWidth p μ)) : Prop :=
  (reduction bank).map (wordValue p μ) = reductionData c ∧
  denoteQuad p μ c (unit bank) = 1 ∧
  wordValue p μ (bank 69) = -1 ∧ wordValue p μ (bank 70) = 0

theorem multiplyCode_denote (bank : Bank (baseWidth p μ))
    (h : Constants p μ c bank) :
    denoteQuad p μ c (output (scriptEval p μ M multiplyCode bank)) =
      denoteQuad p μ c (left bank) * denoteQuad p μ c (right bank) := by
  rw [multiplyCode_output]
  exact SubexpPreparedQuartic.binaryMul_quotient p μ M c _ _ _ h.1

omit [Fact p.Prime] in
theorem constants_frame (a b : Bank (baseWidth p μ))
    (h : ∀ j : Fin 71, j.val < 4 ∨ 65 ≤ j.val → b j = a j)
    (ha : Constants p μ c a) : Constants p μ c b := by
  have hr : reduction b = reduction a := by
    apply quad_ext <;> exact h _ (by decide)
  have hu : unit b = unit a := by
    apply quad_ext <;> exact h _ (by decide)
  exact ⟨by simpa [hr] using ha.1, by simpa [hu] using ha.2.1,
    by simpa [h 69 (by decide)] using ha.2.2.1,
    by simpa [h 70 (by decide)] using ha.2.2.2⟩

theorem multiplyCode_constants (bank : Bank (baseWidth p μ))
    (h : Constants p μ c bank) : Constants p μ c (scriptEval p μ M multiplyCode bank) := by
  apply constants_frame p μ c bank _ _ h
  intro j hj
  apply multiplyCode_frame p μ M bank j
  omega

theorem multiplyCode_left (bank : Bank (baseWidth p μ)) :
    left (scriptEval p μ M multiplyCode bank) = left bank := by
  apply quad_ext <;> dsimp only [left, lowerBank, mulLeft] <;>
    apply multiplyCode_frame <;> decide

theorem multiplyCode_right (bank : Bank (baseWidth p μ)) :
    right (scriptEval p μ M multiplyCode bank) = right bank := by
  apply quad_ext <;> dsimp only [right, lowerBank, mulRight] <;>
    apply multiplyCode_frame <;> decide

theorem multiplyCode_cached (bank : Bank (baseWidth p μ)) :
    cached (scriptEval p μ M multiplyCode bank) = cached bank := by
  apply quad_ext <;> dsimp only [cached] <;> apply multiplyCode_frame <;> decide

theorem accumulateCode_right (bank : Bank (baseWidth p μ)) :
    right (scriptEval p μ M accumulateCode bank) =
      (SubexpPreparedQuartic.binaryAdd p μ M (output bank) (unit bank)).1 := by
  rfl

theorem accumulateCode_denote (bank : Bank (baseWidth p μ))
    (h : Constants p μ c bank) :
    denoteQuad p μ c (right (scriptEval p μ M accumulateCode bank)) =
      denoteQuad p μ c (output bank) + 1 := by
  rw [accumulateCode_right]
  change quotientDenote c _ = _
  rw [SubexpPreparedQuartic.binaryAdd_quotient]
  exact congrArg (fun x => denoteQuad p μ c (output bank) + x) h.2.1

theorem accumulateCode_frame (bank : Bank (baseWidth p μ))
    (j : Fin 71) (hj : j.val < 8 ∨ 12 ≤ j.val) :
    scriptEval p μ M accumulateCode bank j = bank j := by
  apply scriptEval_frame
  have hd : ∀ i ∈ accumulateCode, 8 ≤ i.dst.val ∧ i.dst.val < 12 := by decide
  intro i hi he
  have hh := hd i hi
  rw [he] at hh
  omega

theorem body_constants (bank : Bank (baseWidth p μ)) (h : Constants p μ c bank) :
    Constants p μ c (scriptEval p μ M bodyCode bank) := by
  rw [bodyCode, scriptEval_append]
  apply constants_frame p μ c (scriptEval p μ M multiplyCode bank) _ _
    (multiplyCode_constants p μ M c bank h)
  intro j hj
  apply accumulateCode_frame
  omega

theorem body_left (bank : Bank (baseWidth p μ)) :
    left (scriptEval p μ M bodyCode bank) = left bank := by
  rw [bodyCode, scriptEval_append]
  have hh : left (scriptEval p μ M accumulateCode (scriptEval p μ M multiplyCode bank)) =
      left (scriptEval p μ M multiplyCode bank) := by
    apply quad_ext <;> dsimp only [left, lowerBank, mulLeft] <;>
      apply accumulateCode_frame <;> decide
  rw [hh, multiplyCode_left]

theorem body_cached (bank : Bank (baseWidth p μ)) :
    cached (scriptEval p μ M bodyCode bank) = cached bank := by
  rw [bodyCode, scriptEval_append]
  have hh : cached (scriptEval p μ M accumulateCode (scriptEval p μ M multiplyCode bank)) =
      cached (scriptEval p μ M multiplyCode bank) := by
    apply quad_ext <;> dsimp only [cached] <;> apply accumulateCode_frame <;> decide
  rw [hh, multiplyCode_cached]

theorem body_denote (bank : Bank (baseWidth p μ)) (h : Constants p μ c bank) :
    denoteQuad p μ c (right (scriptEval p μ M bodyCode bank)) =
      denoteQuad p μ c (left bank) * denoteQuad p μ c (right bank) + 1 := by
  rw [bodyCode, scriptEval_append,
    accumulateCode_denote p μ M c _ (multiplyCode_constants p μ M c bank h),
    multiplyCode_denote p μ M c bank h]

theorem safeCode_constants (code : List (SubexponentialSAT.SubexpQuarticMachine.Instr 71))
    (hd : ∀ i ∈ code, 4 ≤ i.dst.val ∧ i.dst.val < 65)
    (bank : Bank (baseWidth p μ)) (h : Constants p μ c bank) :
    Constants p μ c (scriptEval p μ M code bank) := by
  apply constants_frame p μ c bank _ _ h
  intro j hj
  apply scriptEval_frame
  intro i hi he
  have hh := hd i hi
  rw [he] at hh
  omega

theorem cacheCode_left (bank : Bank (baseWidth p μ)) :
    left (scriptEval p μ M cacheCode bank) = left bank := by
  apply quad_ext <;> dsimp only [left, lowerBank, mulLeft] <;> apply scriptEval_frame <;> decide

theorem cacheCode_right (bank : Bank (baseWidth p μ)) :
    right (scriptEval p μ M cacheCode bank) = right bank := by
  apply quad_ext <;> dsimp only [right, lowerBank, mulRight] <;> apply scriptEval_frame <;> decide

theorem cacheCode_cached (bank : Bank (baseWidth p μ)) (hz : wordValue p μ (bank 70) = 0) :
    (cached (scriptEval p μ M cacheCode bank)).map (wordValue p μ) =
      (right bank).map (wordValue p μ) := by
  apply quad_ext <;>
    simp [cached, right, lowerBank, mulRight, cacheCode, scriptEval, Instr.eval,
      ScalarOp.eval, Quad.map, SubexpPreparedQuartic.wordAdd_correct, hz]

theorem negateCode_left (bank : Bank (baseWidth p μ)) (hn : wordValue p μ (bank 69) = -1) :
    (left (scriptEval p μ M negateCode bank)).map (wordValue p μ) =
      ((output bank).map (wordValue p μ)).map Neg.neg := by
  apply quad_ext <;>
    simp [left, output, lowerBank, mulLeft, mulOutput, negateCode, scriptEval, Instr.eval,
      ScalarOp.eval, Quad.map, SubexpPreparedQuartic.wordMul_correct, hn]

theorem negateCode_denote (bank : Bank (baseWidth p μ)) (hn : wordValue p μ (bank 69) = -1) :
    denoteQuad p μ c (left (scriptEval p μ M negateCode bank)) =
      -denoteQuad p μ c (output bank) := by
  unfold denoteQuad
  rw [negateCode_left p μ M bank hn, quotientDenote_neg]

theorem defectCode_left (bank : Bank (baseWidth p μ)) :
    left (scriptEval p μ M defectCode bank) =
      (SubexpPreparedQuartic.binaryAdd p μ M (left bank) (unit bank)).1 := by
  rfl

theorem defectCode_denote (bank : Bank (baseWidth p μ)) (h : Constants p μ c bank) :
    denoteQuad p μ c (left (scriptEval p μ M defectCode bank)) =
      denoteQuad p μ c (left bank) + 1 := by
  rw [defectCode_left]
  change quotientDenote c _ = _
  rw [SubexpPreparedQuartic.binaryAdd_quotient]
  exact congrArg (fun x => denoteQuad p μ c (left bank) + x) h.2.1

theorem zeroCode_left (bank : Bank (baseWidth p μ)) :
    left (scriptEval p μ M zeroCode bank) = left bank := by
  apply quad_ext <;> dsimp only [left, lowerBank, mulLeft] <;> apply scriptEval_frame <;> decide

theorem zeroCode_right (bank : Bank (baseWidth p μ)) (hz : wordValue p μ (bank 70) = 0) :
    (right (scriptEval p μ M zeroCode bank)).map (wordValue p μ) =
      (⟨0, 0, 0, 0⟩ : Quad (ZMod (p^μ))) := by
  apply quad_ext <;>
    simp [right, lowerBank, mulRight, zeroCode, scriptEval, Instr.eval,
      ScalarOp.eval, Quad.map, SubexpPreparedQuartic.wordAdd_correct, hz]

theorem initializeCode_cached (bank : Bank (baseWidth p μ))
    (hz : wordValue p μ (bank 70) = 0) :
    (cached (scriptEval p μ M initializeCode bank)).map (wordValue p μ) =
      (right bank).map (wordValue p μ) := by
  have he : initializeCode = cacheCode ++ (multiplyCode ++ negateCode ++ defectCode ++ zeroCode) := rfl
  rw [he, scriptEval_append]
  have hframe : cached (scriptEval p μ M (multiplyCode ++ negateCode ++ defectCode ++ zeroCode)
      (scriptEval p μ M cacheCode bank)) = cached (scriptEval p μ M cacheCode bank) := by
    apply quad_ext <;> dsimp only [cached] <;> apply scriptEval_frame <;> decide
  rw [hframe, cacheCode_cached p μ M bank hz]

theorem initializeCode_spec (bank : Bank (baseWidth p μ)) (h : Constants p μ c bank) :
    Constants p μ c (scriptEval p μ M initializeCode bank) ∧
    denoteQuad p μ c (left (scriptEval p μ M initializeCode bank)) =
      1 - denoteQuad p μ c (left bank) * denoteQuad p μ c (right bank) ∧
    denoteQuad p μ c (right (scriptEval p μ M initializeCode bank)) = 0 ∧
    denoteQuad p μ c (cached (scriptEval p μ M initializeCode bank)) =
      denoteQuad p μ c (right bank) := by
  let b1 := scriptEval p μ M cacheCode bank
  let b2 := scriptEval p μ M multiplyCode b1
  let b3 := scriptEval p μ M negateCode b2
  let b4 := scriptEval p μ M defectCode b3
  let b5 := scriptEval p μ M zeroCode b4
  have h1 : Constants p μ c b1 := safeCode_constants p μ M c cacheCode (by decide) bank h
  have h2 : Constants p μ c b2 := multiplyCode_constants p μ M c b1 h1
  have h3 : Constants p μ c b3 := safeCode_constants p μ M c negateCode (by decide) b2 h2
  have h4 : Constants p μ c b4 := safeCode_constants p μ M c defectCode (by decide) b3 h3
  have h5 : Constants p μ c b5 := safeCode_constants p μ M c zeroCode (by decide) b4 h4
  have he : scriptEval p μ M initializeCode bank = b5 := by
    simp only [initializeCode, scriptEval_append, b1, b2, b3, b4, b5]
  refine ⟨he.symm ▸ h5, ?_, ?_, ?_⟩
  · rw [he, zeroCode_left, defectCode_denote p μ M c b3 h3,
      negateCode_denote p μ M c b2 h2.2.2.1, multiplyCode_denote p μ M c b1 h1,
      cacheCode_left, cacheCode_right]
    ring
  · rw [he]
    change quotientDenote c ((right b5).map (wordValue p μ)) = 0
    rw [zeroCode_right p μ M b4 h4.2.2.2, quotientDenote_const, map_zero]
  · unfold denoteQuad
    rw [initializeCode_cached p μ M bank h.2.2.2]

theorem restoreCode_right (bank : Bank (baseWidth p μ)) :
    right (scriptEval p μ M restoreCode bank) = right bank := by
  apply quad_ext <;> dsimp only [right, lowerBank, mulRight] <;> apply scriptEval_frame <;> decide

theorem restoreCode_left (bank : Bank (baseWidth p μ)) (hz : wordValue p μ (bank 70) = 0) :
    (left (scriptEval p μ M restoreCode bank)).map (wordValue p μ) =
      (cached bank).map (wordValue p μ) := by
  apply quad_ext <;>
    simp [left, cached, lowerBank, mulLeft, restoreCode, scriptEval, Instr.eval,
      ScalarOp.eval, Quad.map, SubexpPreparedQuartic.wordAdd_correct, hz]

theorem finishCode_denote (bank : Bank (baseWidth p μ)) (h : Constants p μ c bank) :
    denoteQuad p μ c (output (scriptEval p μ M finishCode bank)) =
      denoteQuad p μ c (cached bank) * denoteQuad p μ c (right bank) := by
  have hr := safeCode_constants p μ M c restoreCode (by decide) bank h
  rw [finishCode, scriptEval_append, multiplyCode_denote p μ M c _ hr, restoreCode_right]
  unfold denoteQuad
  rw [restoreCode_left p μ M bank h.2.2.2]

theorem iterate_body_spec (bank : Bank (baseWidth p μ)) (h : Constants p μ c bank)
    (hz : denoteQuad p μ c (right bank) = 0) (n : ℕ) :
    Constants p μ c ((scriptEval p μ M bodyCode)^[n] bank) ∧
    left ((scriptEval p μ M bodyCode)^[n] bank) = left bank ∧
    cached ((scriptEval p μ M bodyCode)^[n] bank) = cached bank ∧
    denoteQuad p μ c (right ((scriptEval p μ M bodyCode)^[n] bank)) =
      (SubexpResidueInverse.geometricHornerWithCost (denoteQuad p μ c (left bank)) n).1 := by
  induction n with
  | zero => exact ⟨h, rfl, rfl, hz⟩
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    refine ⟨body_constants p μ M c _ ih.1,
      (body_left p μ M _).trans ih.2.1,
      (body_cached p μ M _).trans ih.2.2.1, ?_⟩
    rw [body_denote p μ M c _ ih.1, ih.2.1, ih.2.2.2]
    rfl

theorem runBank_denote (bank : Bank (baseWidth p μ)) (h : Constants p μ c bank) (n : ℕ) :
    denoteQuad p μ c (output (runBank p μ M n bank)) =
      NilpotentDefect.geometricInverse (denoteQuad p μ c (left bank))
        (denoteQuad p μ c (right bank)) n := by
  obtain ⟨hi, hl, hr, hb⟩ := initializeCode_spec p μ M c bank h
  obtain ⟨hn, hnl, hnb, hnv⟩ := iterate_body_spec p μ M c _ hi hr n
  rw [runBank, finishCode_denote p μ M c _ hn, hnb, hnv, hb, hl,
    SubexpResidueInverse.geometricHorner_value]
  rfl

theorem runBank_inverse (bank : Bank (baseWidth p μ)) (h : Constants p μ c bank) (n : ℕ)
    (hnil : (1 - denoteQuad p μ c (left bank) * denoteQuad p μ c (right bank)) ^ n = 0) :
    denoteQuad p μ c (output (runBank p μ M n bank)) * denoteQuad p μ c (left bank) = 1 := by
  rw [runBank_denote p μ M c bank h n]
  exact NilpotentDefect.geometricInverse_mul _ _ _ hnil

theorem runBank_inverseWithCost (bank : Bank (baseWidth p μ)) (h : Constants p μ c bank)
    (q n : ℕ) (hb : denoteQuad p μ c (right bank) = denoteQuad p μ c (left bank) ^ (q - 2)) :
    denoteQuad p μ c (output (runBank p μ M n bank)) =
      (SubexpResidueInverse.inverseWithCost q n (denoteQuad p μ c (left bank))).1 := by
  rw [runBank_denote p μ M c bank h n, hb, SubexpResidueInverse.inverseWithCost_value]

/-- The actual finite program returns a multiplicative inverse under the
independent nilpotence condition supplied by the residue-field argument. -/
theorem inverse_correct (regs : Fin 8 → Bool) (bank : Bank (baseWidth p μ)) (counter : List Bool)
    (h : Constants p μ c bank)
    (hnil : (1 - denoteQuad p μ c (left bank) * denoteQuad p μ c (right bank)) ^
      CounterPrograms.value counter = 0) :
    ∃ finalRegs finalCounter,
      RunsIn inverseProgram
        (instructionBound (baseWidth p μ) counter.length (CounterPrograms.value counter))
        ((extendedState regs bank M.bits counter []).withPC (some inverseProgram.entry))
        ((extendedState finalRegs (runBank p μ M (CounterPrograms.value counter) bank)
          M.bits finalCounter []).withPC none) ∧
      denoteQuad p μ c (output (runBank p μ M (CounterPrograms.value counter) bank)) *
        denoteQuad p μ c (left bank) = 1 ∧
      CounterPrograms.value finalCounter = 0 ∧ finalCounter.length = counter.length := by
  obtain ⟨rf, counter', ht, hz, hl⟩ := inverse_execute p μ M regs bank counter
  exact ⟨rf, counter', ht, runBank_inverse p μ M c bank h _ hnil, hz, hl⟩

theorem inverse_correct_primitive (regs : Fin 8 → Bool)
    (bank : Bank (baseWidth p μ)) (counter : List Bool)
    (h : Constants p μ c bank)
    (hnil : (1 - denoteQuad p μ c (left bank) * denoteQuad p μ c (right bank)) ^
      CounterPrograms.value counter = 0) :
    ∃ finalRegs finalCounter,
      Computation.RunsIn (primitive inverseProgram).step
        (primitiveOverhead inverseProgram *
          instructionBound (baseWidth p μ) counter.length (CounterPrograms.value counter))
        (primitiveCfg inverseProgram
          ((extendedState regs bank M.bits counter []).withPC (some inverseProgram.entry)))
        (primitiveCfg inverseProgram
          ((extendedState finalRegs (runBank p μ M (CounterPrograms.value counter) bank)
            M.bits finalCounter []).withPC none)) ∧
      denoteQuad p μ c (output (runBank p μ M (CounterPrograms.value counter) bank)) *
        denoteQuad p μ c (left bank) = 1 ∧
      CounterPrograms.value finalCounter = 0 ∧ finalCounter.length = counter.length := by
  obtain ⟨rf, counter', ht, hv, hz, hl⟩ := inverse_correct p μ M c regs bank counter h hnil
  exact ⟨rf, counter', BitProgram.primitive_execution _ ht, hv, hz, hl⟩

end Semantics

end SubexponentialSAT.SubexpInverseProgram

end OAI.Algorithms
