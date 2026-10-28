import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.PowerCalls
import OAI.Algorithms.SubexponentialSAT.CounterPrograms

namespace OAI.Algorithms

/-!
# Preserving setup of a factor-local assignment count

The fixed program copies a unary arity, counts the copy into a binary exponent,
and invokes the actual preserving power routine.  The base and unary arity are
retained verbatim.  The number of bits in either input is runtime data.
-/

namespace SubexponentialSAT.SubexpFactorCountSetup

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 8 13

def lengthRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def lengthPorts : Fin 3 → Fin 13 := ![4, 2, 5]

theorem lengthRegisters_injective : Function.Injective lengthRegisters := by
  intro a b h
  have hh := congrArg (fun j : Fin 8 => j.val) h
  exact Fin.ext hh

theorem lengthPorts_injective : Function.Injective lengthPorts := by decide

abbrev lengthProgram : Program 8 13 14 :=
  ProgramLinking.liftProgram CounterPrograms.lengthProgram lengthRegisters lengthPorts

def powerPorts : PowerCalls.Ports 13 where
  base := 0
  exponent := 2
  out := 3
  work := ⟨fun i => ⟨6 + i.val, by omega⟩, by
    intro a b h
    apply Fin.ext
    have hh := congrArg Fin.val h
    simp only at hh
    omega⟩
  out_ne_base := by decide
  out_ne_exponent := by decide
  work_ne_base := by
    intro i h
    have hh := congrArg (fun j : Fin 13 => j.val) h
    change 6 + i.val = 0 at hh
    omega
  work_ne_exponent := by
    intro i h
    have hh := congrArg (fun j : Fin 13 => j.val) h
    change 6 + i.val = 2 at hh
    omega
  work_ne_out := by
    intro i h
    have hh := congrArg (fun j : Fin 13 => j.val) h
    change 6 + i.val = 3 at hh
    omega

abbrev resetAccumulator : Cmd 8 13 := .base (.atom (.set 2 false))

abbrev countCommand : Cmd 8 13 :=
  .seq (ArithmeticCalls.copyAt 1 4 5)
    (.seq resetAccumulator (.call lengthProgram))

abbrev command : Cmd 8 13 := .seq countCommand (PowerCalls.powerAt powerPorts)

def countProgram := compiled countCommand (1 : Fin 13) 2

def program := compiled command (0 : Fin 13) 3

def afterLength (d : Data) (exponent : List Bool) : Data :=
  ⟨fun j => if j.val < 3 then false else d.regs j,
    Function.update (Function.update d.stacks 4 []) 2 exponent⟩

private def lengthInput (d : Data) : State 3 3 :=
  ⟨CounterPrograms.counterRegs (d.regs 0) (d.regs 1) false,
    CounterPrograms.lengthStacks (d.stacks 4) [] []⟩

private def lengthOutput (exponent : List Bool) : State 3 3 :=
  ⟨fun _ => false, fun j => if j = 1 then exponent else []⟩

private theorem length_embed_input (d : Data) (h2 : d.stacks 2 = [])
    (h5 : d.stacks 5 = []) (hz : d.regs 2 = false) :
    embedState lengthRegisters lengthPorts d (lengthInput d) = d := by
  apply embedState_eq_of_ports _ _ _ _ _ lengthRegisters_injective lengthPorts_injective
  · intro i
    fin_cases i <;> simp [lengthInput, lengthRegisters, CounterPrograms.counterRegs, hz]
  · intro i hi; rfl
  · intro i
    fin_cases i <;> simp [lengthInput, lengthPorts, CounterPrograms.lengthStacks, h2, h5]
  · intro i hi; rfl

private theorem length_embed_output (d : Data) (h5 : d.stacks 5 = [])
    (exponent : List Bool) :
    embedState lengthRegisters lengthPorts d (lengthOutput exponent) =
      afterLength d exponent := by
  apply embedState_eq_of_ports _ _ _ _ _ lengthRegisters_injective lengthPorts_injective
  · intro i
    fin_cases i <;> simp [afterLength, lengthOutput, lengthRegisters]
  · intro j hj
    have hlarge : ¬ j.val < 3 := by
      intro hsmall
      apply hj
      exact ⟨⟨j.val, hsmall⟩, Fin.ext rfl⟩
    simp [afterLength, hlarge]
  · intro i
    fin_cases i <;> simp [lengthOutput, afterLength, lengthPorts, h5]
  · intro j hj
    have h4 : j ≠ 4 := fun h => hj ⟨0, by simpa [lengthPorts] using h.symm⟩
    have h2 : j ≠ 2 := fun h => hj ⟨1, by simpa [lengthPorts] using h.symm⟩
    simp [afterLength, h4, h2]

/-- The copied unary input is consumed, with the binary count in port 2. -/
theorem length_eval (d : Data) (h2 : d.stacks 2 = []) (h5 : d.stacks 5 = [])
    (hz : d.regs 2 = false) :
    ∃ t ≤ (d.stacks 4).length * (8 * (d.stacks 4).length + 10) + 3,
      ∃ exponent : List Bool,
        Eval (.call lengthProgram) t d (afterLength d exponent) ∧
        BinaryArithmetic.toNat exponent = (d.stacks 4).length ∧
        exponent.length ≤ (d.stacks 4).length := by
  obtain ⟨exponent, hv, hl, t, ht, trace⟩ :=
    CounterPrograms.length_correct_from (d.regs 0) (d.regs 1) (d.stacks 4)
  change Trace CounterPrograms.lengthProgram t
    ((lengthInput d).withPC (some CounterPrograms.lengthProgram.entry))
    ((lengthOutput exponent).withPC none) at trace
  have run := eval_call_lifted CounterPrograms.lengthProgram lengthRegisters lengthPorts d
    lengthRegisters_injective lengthPorts_injective trace
  rw [length_embed_input d h2 h5 hz, length_embed_output d h5 exponent] at run
  exact ⟨t, ht, exponent, run, (CounterPrograms.value_eq_toNat exponent).symm.trans hv, hl⟩

def countBudget (arity : ℕ) : ℕ :=
  (7 * arity + 6) + (arity * (8 * arity + 10) + 3)

/-- A reusable preserving unary-to-binary counter, with only three initially
empty assigned work/output stacks. All other caller stacks are arbitrary. -/
theorem count_eval (d : Data)
    (h2 : d.stacks 2 = []) (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = []) :
    ∃ t ≤ countBudget (d.stacks 1).length,
      ∃ (rf : Fin 8 → Bool) (exponent : List Bool),
        Eval countCommand t d ⟨rf, Function.update d.stacks 2 exponent⟩ ∧
        BinaryArithmetic.toNat exponent = (d.stacks 1).length ∧
        exponent.length ≤ (d.stacks 1).length := by
  let copied := ArithmeticCalls.afterCopy 1 4 d
  let ready : Data := ⟨Function.update copied.regs 2 false, copied.stacks⟩
  have hc : Eval (ArithmeticCalls.copyAt 1 4 5) (7 * (d.stacks 1).length + 5) d copied :=
    ArithmeticCalls.copyAt_eval 1 4 5 d (by decide) (by decide) (by decide) h4 h5
  have hr : Eval resetAccumulator 1 copied ready := .base (.atom _ _)
  have hready2 : ready.stacks 2 = [] := by
    simpa [ready, copied, ArithmeticCalls.afterCopy] using h2
  have hready5 : ready.stacks 5 = [] := by
    simpa [ready, copied, ArithmeticCalls.afterCopy] using h5
  obtain ⟨tl, htl, exponent, hl, he, hel⟩ :=
    length_eval ready hready2 hready5 (by simp [ready])
  let counted := afterLength ready exponent
  have hcounted : counted.stacks = Function.update d.stacks 2 exponent := by
    funext j
    by_cases h2 : j = 2
    · subst j; simp [counted, afterLength]
    · by_cases h4 : j = 4
      · subst j
        simp_all [counted, afterLength]
      · simp [counted, afterLength, ready, copied, ArithmeticCalls.afterCopy, h2, h4]
  have hexponent : BinaryArithmetic.toNat exponent = (d.stacks 1).length := by
    simpa [ready, copied, ArithmeticCalls.afterCopy] using he
  have hexponentLength : exponent.length ≤ (d.stacks 1).length := by
    simpa [ready, copied, ArithmeticCalls.afterCopy] using hel
  have hlengthBound : tl ≤ (d.stacks 1).length * (8 * (d.stacks 1).length + 10) + 3 := by
    simpa [ready, copied, ArithmeticCalls.afterCopy] using htl
  have hstate : counted = ⟨counted.regs, Function.update d.stacks 2 exponent⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · exact hcounted
  refine ⟨(7 * (d.stacks 1).length + 5) + (1 + tl), ?_,
    counted.regs, exponent, ?_, hexponent, hexponentLength⟩
  · unfold countBudget
    omega
  · have run := hc.seq (hr.seq hl)
    change Eval countCommand _ d counted at run
    rwa [hstate] at run

/-- A polynomial in the base width and unary arity, including all setup calls. -/
def budget (baseWidth arity : ℕ) : ℕ :=
  countBudget arity +
    (arity * (50 * (baseWidth + 1) * (2 + (arity + 1) * baseWidth)) +
      (arity + 1) * (16 * arity + 16) + 9 * arity + 11)

/-- The only changed stacks are the binary exponent and the binary fuel.
Every work stack is restored to its initial empty state. -/
theorem setup_eval (d : Data)
    (hclean : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → d.stacks j = []) :
    ∃ t ≤ budget (d.stacks 0).length (d.stacks 1).length,
      ∃ (rf : Fin 8 → Bool) (exponent fuel : List Bool),
        Eval command t d
          ⟨rf, Function.update (Function.update d.stacks 2 exponent) 3 fuel⟩ ∧
        BinaryArithmetic.toNat exponent = (d.stacks 1).length ∧
        exponent.length ≤ (d.stacks 1).length ∧
        BinaryArithmetic.toNat fuel =
          BinaryArithmetic.toNat (d.stacks 0) ^ (d.stacks 1).length ∧
        fuel.length ≤ 1 + (d.stacks 1).length * (d.stacks 0).length := by
  obtain ⟨tc, htc, rc, exponent, hc, hexponent, hexponentLength⟩ :=
    count_eval d (hclean 2 (by decide) (by decide))
      (hclean 4 (by decide) (by decide)) (hclean 5 (by decide) (by decide))
  let counted : Data := ⟨rc, Function.update d.stacks 2 exponent⟩
  have hcounted : counted.stacks = Function.update d.stacks 2 exponent := rfl
  have hv : PowerCalls.Valid powerPorts counted := by
    constructor
    · change counted.stacks 3 = []
      rw [hcounted]
      simpa using hclean 3 (by decide) (by decide)
    · intro i
      change counted.stacks ⟨6 + i.val, by omega⟩ = []
      rw [hcounted]
      have h0 : (⟨6 + i.val, by omega⟩ : Fin 13) ≠ 0 := by
        intro h; have hh := congrArg Fin.val h; simp only at hh; omega
      have h1 : (⟨6 + i.val, by omega⟩ : Fin 13) ≠ 1 := by
        intro h; have hh := congrArg Fin.val h; simp only at hh; omega
      have h2 : (⟨6 + i.val, by omega⟩ : Fin 13) ≠ 2 := by
        intro h; have hh := congrArg Fin.val h; simp only at hh; omega
      simpa [h2] using hclean _ h0 h1
  obtain ⟨tp, rf, fuel, hp, hvalue, hlength, htp⟩ := PowerCalls.powerAt_spec powerPorts counted hv
  have hbase : counted.stacks powerPorts.base = d.stacks 0 := by simp [powerPorts, hcounted]
  have hexp : counted.stacks powerPorts.exponent = exponent := by simp [powerPorts, hcounted]
  rw [hbase, hexp, hexponent] at hvalue hlength
  rw [hbase, hexp] at htp
  have hpowerBound : tp ≤
      (d.stacks 1).length * (50 * ((d.stacks 0).length + 1) *
        (2 + ((d.stacks 1).length + 1) * (d.stacks 0).length)) +
      ((d.stacks 1).length + 1) * (16 * (d.stacks 1).length + 16) +
      9 * (d.stacks 1).length + 11 := by
    apply htp.trans
    simp only [PowerPrograms.runtimeBound, PowerPrograms.workBound,
      PowerPrograms.callbackBound, hexponent]
    have hm := Nat.mul_le_mul_left (16 : ℕ) hexponentLength
    have hm' := Nat.mul_le_mul_left ((d.stacks 1).length + 1)
      (Nat.add_le_add_right hm 16)
    have hn := Nat.mul_le_mul_left (9 : ℕ) hexponentLength
    omega
  refine ⟨tc + tp, ?_,
    rf, exponent, fuel, ?_, hexponent, hexponentLength, hvalue, hlength⟩
  · unfold budget
    omega
  · have run := hc.seq hp
    simpa only [command, counted, powerPorts, hcounted] using run

theorem program_runsIn (d : Data)
    (hclean : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → d.stacks j = []) :
    ∃ (rf : Fin 8 → Bool) (exponent fuel : List Bool),
      RunsIn program (budget (d.stacks 0).length (d.stacks 1).length + 1)
        (d.withPC (some program.entry))
        ((⟨rf, Function.update (Function.update d.stacks 2 exponent) 3 fuel⟩ : Data).withPC none) ∧
      BinaryArithmetic.toNat exponent = (d.stacks 1).length ∧
      exponent.length ≤ (d.stacks 1).length ∧
      BinaryArithmetic.toNat fuel =
        BinaryArithmetic.toNat (d.stacks 0) ^ (d.stacks 1).length ∧
      fuel.length ≤ 1 + (d.stacks 1).length * (d.stacks 0).length := by
  obtain ⟨t, ht, rf, exponent, fuel, heval, he, hel, hf, hfl⟩ := setup_eval d hclean
  exact ⟨rf, exponent, fuel, ⟨t + 1, Nat.add_le_add_right ht 1,
    compiled_halt_trace heval 0 3⟩, he, hel, hf, hfl⟩

theorem count_program_runsIn (d : Data)
    (h2 : d.stacks 2 = []) (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = []) :
    ∃ (rf : Fin 8 → Bool) (exponent : List Bool),
      RunsIn countProgram (countBudget (d.stacks 1).length + 1)
        (d.withPC (some countProgram.entry))
        ((⟨rf, Function.update d.stacks 2 exponent⟩ : Data).withPC none) ∧
      BinaryArithmetic.toNat exponent = (d.stacks 1).length ∧
      exponent.length ≤ (d.stacks 1).length := by
  obtain ⟨t, ht, rf, exponent, heval, he, hel⟩ := count_eval d h2 h4 h5
  exact ⟨rf, exponent, ⟨t + 1, Nat.add_le_add_right ht 1,
    compiled_halt_trace heval 1 2⟩, he, hel⟩

theorem program_primitive (d : Data)
    (hclean : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → d.stacks j = []) :
    ∃ (rf : Fin 8 → Bool) (exponent fuel : List Bool),
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (budget (d.stacks 0).length (d.stacks 1).length + 1))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program
          ((⟨rf, Function.update (Function.update d.stacks 2 exponent) 3 fuel⟩ : Data).withPC none)) ∧
      BinaryArithmetic.toNat exponent = (d.stacks 1).length ∧
      exponent.length ≤ (d.stacks 1).length ∧
      BinaryArithmetic.toNat fuel =
        BinaryArithmetic.toNat (d.stacks 0) ^ (d.stacks 1).length ∧
      fuel.length ≤ 1 + (d.stacks 1).length * (d.stacks 0).length := by
  obtain ⟨rf, exponent, fuel, run, he, hel, hf, hfl⟩ := program_runsIn d hclean
  exact ⟨rf, exponent, fuel, BitProgram.primitive_execution _ run, he, hel, hf, hfl⟩

end SubexponentialSAT.SubexpFactorCountSetup

end OAI.Algorithms
