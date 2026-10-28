import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientPascalProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation
import OAI.Algorithms.SubexponentialSAT.ExecClauseCost
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-!
# Fixed control for the normalized coefficient equations

The first runtime loop performs `A` weighted Pascal shifts. The second
checks `R` consecutive first entries, alternating the sign, and shifts
again after every check. Every scalar operation and comparison is a call
to an existing finite bit program.
-/

namespace SubexponentialSAT.Subexp.CoefficientCheckerProgram

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

open BitProgram StructuredCalls Subexp.TupleProgram

def lowRegisters (i : Fin 8) : Fin 11 := Fin.castAdd 3 i
def lowStacks (i : Fin 16) : Fin 20 := Fin.castAdd 4 i

theorem lowRegisters_injective : Function.Injective lowRegisters := Fin.castAdd_injective _ _
theorem lowStacks_injective : Function.Injective lowStacks := Fin.castAdd_injective _ _

def wordPorts : RecordPrograms.Ports 11 20 :=
  ⟨0,1,2,10,9,by decide,by decide,by decide,by decide⟩

def equalityRegisters (i : Fin 5) : Fin 11 := Fin.castAdd 6 i
def equalityStacks : Fin 2 → Fin 20 := ![0,1]

theorem equalityRegisters_injective : Function.Injective equalityRegisters := Fin.castAdd_injective _ _
theorem equalityStacks_injective : Function.Injective equalityStacks := by decide

abbrev copy (src dst : Fin 20) : Cmd 11 20 :=
  .call (StackRoutines.copyProgram src dst 9 0 1)

abbrev clear (src : Fin 20) : Cmd 11 20 := .call (StackRoutines.clearProgram src 0 1)
abbrev transfer (src dst : Fin 20) : Cmd 11 20 := .call (StackRoutines.transferProgram src dst 0 1)

abbrev scalarAdd : Cmd 11 20 :=
  .call (ProgramLinking.liftProgram
    (compiled MatrixScalarProgram.add 0 0) lowRegisters lowStacks)

abbrev pascal : Cmd 11 20 :=
  .call (ProgramLinking.liftProgram
    (CoefficientPascalProgram.program true) lowRegisters lowStacks)

/-- The saved dimension is copied for each invocation; the new vector
replaces the current vector only after the Pascal call has finished. -/
abbrev shiftOnce : Cmd 11 20 :=
  .seq (copy 16 15) (.seq pascal
    (.seq (clear 12) (.seq (transfer 8 9) (transfer 9 12))))

abbrev loadHead : Cmd 11 20 :=
  .seq (copy 12 10) (.seq (RecordPrograms.reader wordPorts)
    (.seq (transfer 9 0) (clear 10)))

/-- For a negative target, `x = -1` is tested as `x+1 = 0`. -/
abbrev prepareComparison : Cmd 11 20 :=
  .ite 9 (.seq (copy 19 1) (.seq scalarAdd (copy 14 1))) (copy 19 1)

abbrev equality : Cmd 11 20 :=
  .call (ProgramLinking.liftProgram ExecClauseCost.bitEqualityProgram
    equalityRegisters equalityStacks)

abbrev compareHead : Cmd 11 20 :=
  .seq loadHead (.seq prepareComparison (.seq equality
    (.seq (clear 0) (.seq (clear 1) (.base (.atom (.band 10 10 4)))))))

abbrev toggle : Cmd 11 20 := .base (.atom (.bnot 9 9))
abbrev popA : Cmd 11 20 := .base (.atom (.pop 17 0 8))
abbrev popChecks : Cmd 11 20 := .base (.atom (.pop 18 0 8))

abbrev advance : Cmd 11 20 :=
  .seq popA (.while 8 (.seq shiftOnce (.seq toggle popA)))

abbrev checkConsecutive : Cmd 11 20 :=
  .seq (copy 16 18) (.seq popChecks
    (.while 8 (.seq compareHead (.seq shiftOnce (.seq toggle popChecks)))))

abbrev command : Cmd 11 20 :=
  .seq (.base (.atom (.set 9 false))) (.seq (.base (.atom (.set 10 true)))
    (.seq advance checkConsecutive))

def program := compiled command 12 12

/-- The caller supplies only the canonical field constants and runtime
unary counters; no binomial table or proposed score is an input. -/
def wide (low : MatrixScalarProgram.Data) (guard negative accepted : Bool)
    (dimension advanceCount checkCount one : List Bool) : State 11 20 :=
  ⟨Fin.addCases (m := 8) (n := 3) low.regs ![guard,negative,accepted],
    Fin.addCases (m := 16) (n := 4) low.stacks ![dimension,advanceCount,checkCount,one]⟩

def inputState (p A : ℕ) (xs : List (ZMod p)) (regs : Fin 8 → Bool) : State 11 20 :=
  wide (MatrixScalarProgram.state regs [] [] (MatrixWordEncoding.modulus p) [] [] []
    (CoefficientPascalProgram.valueWords p xs) [] (MatrixWordEncoding.word p 0) [])
    false false true (List.replicate xs.length true) (List.replicate A true) []
    (MatrixWordEncoding.word p 1)


abbrev Data := State 11 20

open SubexpScanPrimitives MatrixWordEncoding

/-- The high three registers and four stacks are a genuine caller frame. -/
theorem embed_wide (before after : MatrixScalarProgram.Data)
    (g neg ok : Bool) (dimension advanceCount checkCount one : List Bool) :
    embedState lowRegisters lowStacks (wide before g neg ok dimension advanceCount checkCount one)
      after = wide after g neg ok dimension advanceCount checkCount one := by
  apply embedState_eq lowRegisters lowStacks lowRegisters_injective lowStacks_injective
  · intro i
    simp [wide, lowRegisters]
  · intro i
    simp [wide, lowStacks]
  · intro j hj
    revert hj
    refine Fin.addCases (m := 8) (n := 3) (fun i => ?_) (fun i => ?_) j
    · intro hi
      exact (hi ⟨i,rfl⟩).elim
    · intro _
      simp [wide]
  · intro j hj
    revert hj
    refine Fin.addCases (m := 16) (n := 4) (fun i => ?_) (fun i => ?_) j
    · intro hi
      exact (hi ⟨i,rfl⟩).elim
    · intro _
      simp [wide]

theorem low_call_eval {l n : ℕ} (p : Program 8 16 l)
    (before after : MatrixScalarProgram.Data)
    (g neg ok : Bool) (dimension advanceCount checkCount one : List Bool)
    (h : Trace p n (before.withPC (some p.entry)) (after.withPC none)) :
    Eval (.call (ProgramLinking.liftProgram p lowRegisters lowStacks)) n
      (wide before g neg ok dimension advanceCount checkCount one)
      (wide after g neg ok dimension advanceCount checkCount one) := by
  simpa only [embed_wide] using
    eval_call_lifted p lowRegisters lowStacks
      (wide before g neg ok dimension advanceCount checkCount one)
      lowRegisters_injective lowStacks_injective h

def cleared (d : Data) (src : Fin 20) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem clear_eval (d : Data) (src : Fin 20) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared d src) := by
  apply Eval.call
  have ht := StackRoutines.halt_after_trace _
    (StackRoutines.clearProgram_trace src (0 : Fin 11) 1 d.regs d.stacks) 2 rfl rfl
  simpa [clear, cleared, StackRoutines.clearResult, StackRoutines.clearProgram,
    StackRoutines.clearStacks, StructuredProgram.State.withPC, Nat.add_assoc] using ht

variable (p : ℕ) [Fact p.Prime]

def lowData (regs : Fin 8 → Bool) (xs : List (ZMod p)) (output count : List Bool) :
    MatrixScalarProgram.Data :=
  MatrixScalarProgram.state regs [] [] (modulus p) output [] []
    (CoefficientPascalProgram.valueWords p xs) [] (word p 0) count

def ready (regs : Fin 8 → Bool) (g neg ok : Bool) (xs : List (ZMod p))
    (advanceCount checkCount : List Bool) : Data :=
  wide (lowData p regs xs [] []) g neg ok (List.replicate xs.length true)
    advanceCount checkCount (word p 1)

def shiftBudget (R B : ℕ) : ℕ :=
  CoefficientPascalProgram.budget R B + 7 * R + 8 * (R * (2 * B + 1)) + 14

private theorem copy_dimension_state (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (a c : List Bool) :
    afterCopy (ready p regs g neg ok xs a c) 16 15 0 1 =
      wide (lowData p (readRegs regs 0 1 none) xs [] (List.replicate xs.length true))
        g neg ok (List.replicate xs.length true) a c (word p 1) := by
  apply state_ext
  · funext j
    fin_cases j <;> simp [afterCopy, ready, wide, lowData,
      MatrixScalarProgram.state, readRegs]
  · funext j
    fin_cases j <;> simp [afterCopy, ready, wide, lowData,
      MatrixScalarProgram.state, MatrixScalarProgram.scalarStacks, StackRoutines.copyStacks]

private theorem replace_output_state (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs ys : List (ZMod p)) (a c : List Bool) (hlen : ys.length = xs.length) :
    afterTransfer (afterTransfer (cleared
      (wide (lowData p regs xs (CoefficientPascalProgram.valueWords p ys) [])
        g neg ok (List.replicate xs.length true) a c (word p 1)) 12) 8 9 0 1) 9 12 0 1 =
      ready p (readRegs regs 0 1 none) g neg ok ys a c := by
  apply state_ext
  · funext j
    fin_cases j <;> simp [afterTransfer, cleared, wide, lowData,
      MatrixScalarProgram.state, ready, readRegs]
  · funext j
    fin_cases j <;> simp [afterTransfer, cleared, wide, lowData,
      MatrixScalarProgram.state, MatrixScalarProgram.scalarStacks, ready,
      StackRoutines.transferStacks, hlen]

/-- One actual weighted Pascal shift, preserving parity, answer, both outer
counters, the saved dimension, and the canonical field constants. -/
theorem shiftOnce_eval (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (advanceCount checkCount : List Bool) :
    ∃ n ≤ shiftBudget xs.length (width p), ∃ regs',
      Eval shiftOnce n (ready p regs g neg ok xs advanceCount checkCount)
        (ready p regs' g neg ok (CoefficientDynamics.shift xs) advanceCount checkCount) := by
  let d₀ := ready p regs g neg ok xs advanceCount checkCount
  let r₁ := readRegs regs 0 1 none
  let d₁ := afterCopy d₀ 16 15 0 1
  have h₁ : Eval (copy 16 15) (7 * xs.length + 5) d₀ d₁ := by
    have h := SubexpScanPrimitives.copy_eval d₀ 16 15 9 0 1
      (by decide) (by decide) (by decide) (by decide)
      (by simp [d₀, ready, wide, lowData, MatrixScalarProgram.state, MatrixScalarProgram.scalarStacks])
    have hlen : (d₀.stacks 16).length = xs.length := by simp [d₀, ready, wide]
    simpa only [copy, hlen] using h
  have hstate₁ : d₁ = wide (lowData p r₁ xs [] (List.replicate xs.length true))
      g neg ok (List.replicate xs.length true) advanceCount checkCount (word p 1) := by
    exact copy_dimension_state p regs g neg ok xs advanceCount checkCount
  obtain ⟨r₂, n, hn, ht⟩ := CoefficientPascalProgram.program_run p true xs r₁
  let ys := CoefficientPascalProgram.shiftBy p true xs
  let d₂ := wide (lowData p r₂ xs (CoefficientPascalProgram.valueWords p ys) [])
    g neg ok (List.replicate xs.length true) advanceCount checkCount (word p 1)
  have h₂ : Eval pascal n d₁ d₂ := by
    have h := low_call_eval (CoefficientPascalProgram.program true)
      (lowData p r₁ xs [] (List.replicate xs.length true))
      (lowData p r₂ xs (CoefficientPascalProgram.valueWords p ys) [])
      g neg ok (List.replicate xs.length true) advanceCount checkCount (word p 1) ht
    rw [← hstate₁] at h
    exact h
  let d₃ := cleared d₂ 12
  let d₄ := afterTransfer d₃ 8 9 0 1
  let d₅ := afterTransfer d₄ 9 12 0 1
  let L := xs.length * (2 * width p + 1)
  have hL : (CoefficientPascalProgram.valueWords p xs).length = L :=
    CoefficientPascalProgram.valueWords_length p xs
  have hY : (CoefficientPascalProgram.valueWords p ys).length = L := by
    simp [ys, CoefficientPascalProgram.valueWords_length, L]
  have h₃ : Eval (clear 12) (2 * L + 3) d₂ d₃ := by
    have hlen : (d₂.stacks 12).length = L := by
      simpa [d₂, wide, lowData, MatrixScalarProgram.state, MatrixScalarProgram.scalarStacks] using hL
    simpa only [hlen] using clear_eval d₂ 12
  have h₄ : Eval (transfer 8 9) (3 * L + 3) d₃ d₄ := by
    have hlen : (d₃.stacks 8).length = L := by
      simpa [d₃, cleared, d₂, wide, lowData, MatrixScalarProgram.state,
        MatrixScalarProgram.scalarStacks] using hY
    simpa only [transfer, hlen] using
      SubexpScanPrimitives.transfer_eval d₃ 8 9 0 1 (by decide) (by decide)
  have h₅ : Eval (transfer 9 12) (3 * L + 3) d₄ d₅ := by
    have hlen : (d₄.stacks 9).length = L := by
      simpa [d₄, afterTransfer, d₃, cleared, d₂, wide, lowData,
        MatrixScalarProgram.state, MatrixScalarProgram.scalarStacks, StackRoutines.transferStacks]
        using hY
    simpa only [transfer, hlen] using
      SubexpScanPrimitives.transfer_eval d₄ 9 12 0 1 (by decide) (by decide)
  let r₅ := readRegs r₂ 0 1 none
  have hfinal : d₅ = ready p r₅ g neg ok (CoefficientDynamics.shift xs) advanceCount checkCount := by
    have h : d₅ = ready p r₅ g neg ok ys advanceCount checkCount :=
      replace_output_state p r₂ g neg ok xs ys advanceCount checkCount
      (by simp [ys])
    exact h.trans (congrArg (fun zs => ready p r₅ g neg ok zs advanceCount checkCount)
      (CoefficientPascalProgram.shiftBy_true p xs))
  have he := h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))
  rw [hfinal] at he
  refine ⟨(7 * xs.length + 5) + (n + ((2 * L + 3) + ((3 * L + 3) + (3 * L + 3)))),
    ?_, r₅, he⟩
  dsimp [shiftBudget, L]
  omega

end SubexponentialSAT.Subexp.CoefficientCheckerProgram

end OAI.Algorithms
