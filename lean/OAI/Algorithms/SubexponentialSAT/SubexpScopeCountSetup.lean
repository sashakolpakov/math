import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSunflowerProgram
import OAI.Algorithms.SubexponentialSAT.SubexpFactorCountSetup
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Actual preserving scope-record count and assignment-fuel setup.
The scope and base remain on stacks 1 and 0. The program returns unary arity,
binary exponent, and binary base^arity on stacks 2, 3, and 4. -/

namespace SubexponentialSAT.SubexpScopeCountSetup

open BitProgram StructuredCalls

abbrev Data := State 8 15

def Ready (d : Data) : Prop := ∀ i : Fin 15, i ≠ 0 → i ≠ 1 → d.stacks i = []

abbrev counterProgram : Program 2 2 13 :=
  { SubexpSunflowerProgram.CountRecords.program with entry := 2 }

def counterState (value present : Bool) (input output : List Bool) : State 2 2 :=
  ⟨ParserProgram.pair value present, ParserProgram.pair input output⟩

theorem counter_trace (records : List (List Bool)) (value present : Bool) :
    Trace counterProgram (SubexpSunflowerProgram.CountRecords.loopSteps records)
      ((counterState value present (Encoding.encodeList id records) []).withPC (some counterProgram.entry))
      ((counterState false false [] (List.replicate records.length true)).withPC none) := by
  have h := SubexpSunflowerProgram.CountRecords.loop_trace records [] [] value present
  simpa [counterProgram, counterState, SubexpSunflowerProgram.CountRecords.cfg] using h

def counterReg (i : Fin 2) : Fin 8 := i.castAdd 6
def counterStack : Fin 2 → Fin 15 := ![14, 2]

theorem counterReg_injective : Function.Injective counterReg := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 8 => i.val) h)

theorem counterStack_injective : Function.Injective counterStack := by decide

abbrev countCall : Cmd 8 15 := .call (ProgramLinking.liftProgram counterProgram counterReg counterStack)

theorem countCall_eval (records : List (List Bool)) (d : Data)
    (hi : d.stacks 14 = Encoding.encodeList id records) (ho : d.stacks 2 = []) :
    ∃ e : Data, Eval countCall (SubexpSunflowerProgram.CountRecords.loopSteps records) d e ∧
      e.stacks = Function.update (Function.update d.stacks 14 []) 2 (List.replicate records.length true) := by
  let a := counterState (d.regs 0) (d.regs 1) (Encoding.encodeList id records) []
  let b := counterState false false [] (List.replicate records.length true)
  have ha : a = projectState counterReg counterStack d := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ counterStack, ParserProgram.pair, hi, ho]
  have ht := counter_trace records (d.regs 0) (d.regs 1)
  change Trace counterProgram _ (a.withPC _) (b.withPC _) at ht
  rw [ha] at ht
  have he := eval_call_from_state counterProgram counterReg counterStack d
    counterReg_injective counterStack_injective ht
  let e := embedState counterReg counterStack d b
  have hs (i : Fin 2) : e.stacks (counterStack i) = b.stacks i :=
    embedState_stack _ _ _ _ counterStack_injective i
  refine ⟨e, he, ?_⟩
  funext i
  by_cases h14 : i = 14
  · subst i
    simpa [b, counterState, counterStack, ParserProgram.pair] using hs 0
  by_cases h2 : i = 2
  · subst i
    simpa [b, counterState, counterStack, ParserProgram.pair] using hs 1
  · rw [embedState_stack_frame counterReg counterStack d b i (by
      rintro ⟨j, hj⟩
      fin_cases j <;> simp [counterStack] at hj <;> simp_all)]
    simp [h14, h2]

abbrev countCommand : Cmd 8 15 := .seq (ArithmeticCalls.copyAt 1 14 5) countCall

def countBudget (records : List (List Bool)) : ℕ :=
  7 * (Encoding.encodeList id records).length + 5 + SubexpSunflowerProgram.CountRecords.loopSteps records

theorem count_eval (records : List (List Bool)) (d : Data)
    (hs : d.stacks 1 = Encoding.encodeList id records)
    (h2 : d.stacks 2 = []) (h5 : d.stacks 5 = []) (h14 : d.stacks 14 = []) :
    ∃ rf : Fin 8 → Bool,
      Eval countCommand (countBudget records) d
        ⟨rf, Function.update d.stacks 2 (List.replicate records.length true)⟩ := by
  let a := ArithmeticCalls.afterCopy 1 14 d
  have ha14 : a.stacks 14 = Encoding.encodeList id records := by
    simp [a, ArithmeticCalls.afterCopy, hs]
  have ha2 : a.stacks 2 = [] := by simpa [a, ArithmeticCalls.afterCopy] using h2
  obtain ⟨e, he, hstacks⟩ := countCall_eval records a ha14 ha2
  have heq : e.stacks = Function.update d.stacks 2 (List.replicate records.length true) := by
    rw [hstacks]
    funext i
    by_cases hi2 : i = 2
    · subst i; simp
    by_cases hi14 : i = 14
    · subst i; simp [h14]
    · simp [a, ArithmeticCalls.afterCopy, hi2, hi14]
  have heq' : e = (⟨e.regs, Function.update d.stacks 2 (List.replicate records.length true)⟩ : Data) :=
    congrArg (fun stk => (⟨e.regs, stk⟩ : Data)) heq
  have hcopy := ArithmeticCalls.copyAt_eval (1 : Fin 15) 14 5 d
    (by decide) (by decide) (by decide) h14 h5
  have hrun := hcopy.seq he
  rw [heq'] at hrun
  refine ⟨e.regs, ?_⟩
  simpa only [countCommand, countBudget, hs] using hrun

def setupStack : Fin 13 → Fin 15 := ![0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
theorem setupStack_injective : Function.Injective setupStack := by decide

abbrev setupCall : Cmd 8 15 := .call (ProgramLinking.liftProgram
  SubexpFactorCountSetup.program id setupStack)

theorem setupCall_eval (d : Data)
    (hc : ∀ i : Fin 15, i ≠ 0 → i ≠ 1 → i ≠ 2 → d.stacks i = []) :
    ∃ n ≤ SubexpFactorCountSetup.budget (d.stacks 0).length (d.stacks 2).length + 1,
      ∃ (e : Data) (exponent fuel : List Bool),
        Eval setupCall n d e ∧ e.stacks = Function.update (Function.update d.stacks 3 exponent) 4 fuel ∧
        BinaryArithmetic.toNat exponent = (d.stacks 2).length ∧ exponent.length ≤ (d.stacks 2).length ∧
        BinaryArithmetic.toNat fuel = BinaryArithmetic.toNat (d.stacks 0) ^ (d.stacks 2).length ∧
        fuel.length ≤ 1 + (d.stacks 2).length * (d.stacks 0).length := by
  let a := projectState id setupStack d
  have ha : ∀ i : Fin 13, i ≠ 0 → i ≠ 1 → a.stacks i = [] := by
    intro i hi0 hi1
    fin_cases i
    · exact (hi0 rfl).elim
    · exact (hi1 rfl).elim
    all_goals exact hc _ (by decide) (by decide) (by decide)
  obtain ⟨rf, exponent, fuel, ⟨n, hn, ht⟩, hexp, hexpLen, hfuel, hfuelLen⟩ :=
    SubexpFactorCountSetup.program_runsIn a ha
  let b : SubexpFactorCountSetup.Data :=
    ⟨rf, Function.update (Function.update a.stacks 2 exponent) 3 fuel⟩
  let e := embedState id setupStack d b
  have he := eval_call_from_state SubexpFactorCountSetup.program id setupStack d
    Function.injective_id setupStack_injective ht
  refine ⟨n, hn, e, exponent, fuel, he, ?_, hexp, hexpLen, hfuel, hfuelLen⟩
  change Function.extend setupStack (Function.update (Function.update a.stacks 2 exponent) 3 fuel) d.stacks = _
  rw [ProgramLinking.extend_update setupStack_injective,
    ProgramLinking.extend_update setupStack_injective]
  have hproject : Function.extend setupStack a.stacks d.stacks = d.stacks :=
    congrArg StructuredProgram.State.stacks
      (embedState_project id setupStack d Function.injective_id setupStack_injective)
  rw [hproject]
  rfl

def outputStacks (d : Data) (arity : ℕ) (exponent fuel : List Bool) : Fin 15 → List Bool :=
  Function.update (Function.update (Function.update d.stacks 2 (List.replicate arity true)) 3 exponent) 4 fuel

abbrev command : Cmd 8 15 := .seq countCommand setupCall

def commandBound (baseWidth : ℕ) (records : List (List Bool)) : ℕ :=
  countBudget records + SubexpFactorCountSetup.budget baseWidth records.length + 1

theorem command_eval (records : List (List Bool)) (d : Data)
    (hs : d.stacks 1 = Encoding.encodeList id records) (hr : Ready d) :
    ∃ n ≤ commandBound (d.stacks 0).length records,
      ∃ (rf : Fin 8 → Bool) (exponent fuel : List Bool),
        Eval command n d ⟨rf, outputStacks d records.length exponent fuel⟩ ∧
        BinaryArithmetic.toNat exponent = records.length ∧ exponent.length ≤ records.length ∧
        BinaryArithmetic.toNat fuel = BinaryArithmetic.toNat (d.stacks 0) ^ records.length ∧
        fuel.length ≤ 1 + records.length * (d.stacks 0).length := by
  obtain ⟨rc, hc⟩ := count_eval records d hs
    (hr 2 (by decide) (by decide)) (hr 5 (by decide) (by decide)) (hr 14 (by decide) (by decide))
  let a : Data := ⟨rc, Function.update d.stacks 2 (List.replicate records.length true)⟩
  have ha : ∀ i : Fin 15, i ≠ 0 → i ≠ 1 → i ≠ 2 → a.stacks i = [] := by
    intro i hi0 hi1 hi2
    simpa [a, hi2] using hr i hi0 hi1
  obtain ⟨n, hn, e, exponent, fuel, he, heStacks, heValue, heLen, hfValue, hfLen⟩ := setupCall_eval a ha
  have heq : e = (⟨e.regs, outputStacks d records.length exponent fuel⟩ : Data) :=
    congrArg (fun stk => (⟨e.regs, stk⟩ : Data)) heStacks
  have hrun := hc.seq he
  rw [heq] at hrun
  refine ⟨countBudget records + n, ?_, e.regs, exponent, fuel, hrun, ?_, ?_, ?_, ?_⟩
  · simpa [a, commandBound, Nat.add_assoc] using Nat.add_le_add_left hn (countBudget records)
  · simpa [a] using heValue
  · simpa [a] using heLen
  · simpa [a] using hfValue
  · simpa [a] using hfLen

def program := compiled command 1 4

theorem program_runsIn (records : List (List Bool)) (d : Data)
    (hs : d.stacks 1 = Encoding.encodeList id records) (hr : Ready d) :
    ∃ (rf : Fin 8 → Bool) (exponent fuel : List Bool),
      RunsIn program (commandBound (d.stacks 0).length records + 1)
        (d.withPC (some program.entry))
        ((⟨rf, outputStacks d records.length exponent fuel⟩ : Data).withPC none) ∧
      BinaryArithmetic.toNat exponent = records.length ∧ exponent.length ≤ records.length ∧
      BinaryArithmetic.toNat fuel = BinaryArithmetic.toNat (d.stacks 0) ^ records.length ∧
      fuel.length ≤ 1 + records.length * (d.stacks 0).length := by
  obtain ⟨n, hn, rf, exponent, fuel, he, hev, hel, hfv, hfl⟩ := command_eval records d hs hr
  exact ⟨rf, exponent, fuel, ⟨n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace he 1 4⟩,
    hev, hel, hfv, hfl⟩

theorem commandBound_polynomial (baseWidth : ℕ) (records : List (List Bool)) :
    commandBound baseWidth records + 1 ≤ 10 * (Encoding.encodeList id records).length +
      SubexpFactorCountSetup.budget baseWidth records.length + 9 := by
  have h := SubexpSunflowerProgram.CountRecords.steps_le_encoded records
  dsimp [commandBound, countBudget, SubexpSunflowerProgram.CountRecords.steps] at *
  omega

theorem primitive_execution (records : List (List Bool)) (d : Data)
    (hs : d.stacks 1 = Encoding.encodeList id records) (hr : Ready d) :
    ∃ (rf : Fin 8 → Bool) (exponent fuel : List Bool),
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (commandBound (d.stacks 0).length records + 1))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program ((⟨rf, outputStacks d records.length exponent fuel⟩ : Data).withPC none)) ∧
      BinaryArithmetic.toNat exponent = records.length ∧ exponent.length ≤ records.length ∧
      BinaryArithmetic.toNat fuel = BinaryArithmetic.toNat (d.stacks 0) ^ records.length ∧
      fuel.length ≤ 1 + records.length * (d.stacks 0).length := by
  obtain ⟨rf, exponent, fuel, hrun, hev, hel, hfv, hfl⟩ := program_runsIn records d hs hr
  exact ⟨rf, exponent, fuel, BitProgram.primitive_execution program hrun, hev, hel, hfv, hfl⟩

/-- The scope representation used by the clause producer is exactly the
generic framed-record representation consumed by this program. -/
theorem encode_scope (scope : List ℕ) :
    Encoding.encodeList id (scope.map Encoding.encodeNat) =
      Encoding.encodeList Encoding.encodeNat scope := by
  induction scope with
  | nil => rfl
  | cons j scope ih => simp [Encoding.encodeList, ih]

theorem outputStacks_frame (d : Data) (arity : ℕ) (exponent fuel : List Bool)
    (i : Fin 15) (h2 : i ≠ 2) (h3 : i ≠ 3) (h4 : i ≠ 4) :
    outputStacks d arity exponent fuel i = d.stacks i := by
  simp [outputStacks, h2, h3, h4]

theorem nat_command_eval (scope : List ℕ) (d : Data)
    (hs : d.stacks 1 = Encoding.encodeList Encoding.encodeNat scope) (hr : Ready d) :
    ∃ n ≤ commandBound (d.stacks 0).length (scope.map Encoding.encodeNat),
      ∃ (rf : Fin 8 → Bool) (exponent fuel : List Bool),
        Eval command n d ⟨rf, outputStacks d scope.length exponent fuel⟩ ∧
        BinaryArithmetic.toNat exponent = scope.length ∧ exponent.length ≤ scope.length ∧
        BinaryArithmetic.toNat fuel = BinaryArithmetic.toNat (d.stacks 0) ^ scope.length ∧
        fuel.length ≤ 1 + scope.length * (d.stacks 0).length := by
  simpa only [List.length_map] using command_eval (scope.map Encoding.encodeNat) d
    (by simpa only [encode_scope] using hs) hr

theorem nat_program_runsIn (scope : List ℕ) (d : Data)
    (hs : d.stacks 1 = Encoding.encodeList Encoding.encodeNat scope) (hr : Ready d) :
    ∃ (rf : Fin 8 → Bool) (exponent fuel : List Bool),
      RunsIn program (commandBound (d.stacks 0).length (scope.map Encoding.encodeNat) + 1)
        (d.withPC (some program.entry))
        ((⟨rf, outputStacks d scope.length exponent fuel⟩ : Data).withPC none) ∧
      BinaryArithmetic.toNat exponent = scope.length ∧ exponent.length ≤ scope.length ∧
      BinaryArithmetic.toNat fuel = BinaryArithmetic.toNat (d.stacks 0) ^ scope.length ∧
      fuel.length ≤ 1 + scope.length * (d.stacks 0).length := by
  simpa only [List.length_map] using program_runsIn (scope.map Encoding.encodeNat) d
    (by simpa only [encode_scope] using hs) hr

end SubexponentialSAT.SubexpScopeCountSetup

end OAI.Algorithms
