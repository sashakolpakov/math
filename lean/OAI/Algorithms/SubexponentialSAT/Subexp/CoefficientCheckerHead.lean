import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientCheckerProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientCheckerSemantics

namespace OAI.Algorithms

/-! Actual preparation and comparison of one normalized coefficient head. -/

namespace SubexponentialSAT.Subexp.CoefficientCheckerProgram

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

open BitProgram StructuredCalls SubexpScanPrimitives MatrixWordEncoding

variable (p : ℕ) [Fact p.Prime]

def operands (regs : Fin 8 → Bool) (g neg ok : Bool) (xs : List (ZMod p))
    (advanceCount checkCount left right : List Bool) : Data :=
  wide (MatrixScalarProgram.state regs left right (modulus p) [] [] []
      (CoefficientPascalProgram.valueWords p xs) [] (word p 0) [])
    g neg ok (List.replicate xs.length true) advanceCount checkCount (word p 1)

@[simp] theorem operands_empty (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (a c : List Bool) :
    operands p regs g neg ok xs a c [] [] = ready p regs g neg ok xs a c := rfl

/-- Unconditional stack lookup separates the finite representation proof
from later excluded-port hypotheses. -/
theorem operands_stack (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (a c left right : List Bool) (j : Fin 20) :
    (operands p regs g neg ok xs a c left right).stacks j =
      if j = 0 then left else if j = 1 then right else
        (ready p regs g neg ok xs a c).stacks j := by
  fin_cases j <;> rfl

theorem scalarAdd_eval (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (a c : List Bool) (x y : ZMod p) :
    ∃ n ≤ 6000 * (width p + 1)^2 + 1, ∃ regs',
      Eval scalarAdd n (operands p regs g neg ok xs a c (word p x) (word p y))
        (operands p regs' g neg ok xs a c (word p (x + y)) []) := by
  obtain ⟨n, hn, r, he⟩ := CoefficientPascalProgram.add_field_eval p x y regs
    [] [] [] (CoefficientPascalProgram.valueWords p xs) [] (word p 0) []
  have ht := compiled_halt_trace he 0 0
  have h := low_call_eval (compiled MatrixScalarProgram.add 0 0) _ _ g neg ok
    (List.replicate xs.length true) a c (word p 1) ht
  exact ⟨n + 1, Nat.add_le_add_right hn 1, r, h⟩

def rightConstant (negative : Bool) : ZMod p := if negative then 0 else 1

def leftAdjusted (negative : Bool) (x : ZMod p) : ZMod p := if negative then x + 1 else x

theorem adjusted_eq_iff (negative : Bool) (x : ZMod p) :
    leftAdjusted p negative x = rightConstant p negative ↔
      x = CoefficientCheckerSemantics.sign negative := by
  cases negative <;> simp [leftAdjusted, rightConstant, CoefficientCheckerSemantics.sign,
    add_eq_zero_iff_eq_neg]

/-- The two copy branches preserve all coefficient and control data. -/
theorem copy_one_eval (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (a c left : List Bool) :
    Eval (copy 19 1) (7 * width p + 5)
      (operands p regs g neg ok xs a c left [])
      (operands p (readRegs regs 0 1 none) g neg ok xs a c left (word p 1)) := by
  let d := operands p regs g neg ok xs a c left []
  have he := SubexpScanPrimitives.copy_eval d 19 1 9 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simp [d, operands, wide, MatrixScalarProgram.scalarStacks])
  have hfinal : afterCopy d 19 1 0 1 =
      operands p (readRegs regs 0 1 none) g neg ok xs a c left (word p 1) := by
    apply state_ext
    · funext j
      fin_cases j <;> simp [d, operands, wide, afterCopy, readRegs]
    · funext j
      fin_cases j <;> simp [d, operands, wide, afterCopy,
        MatrixScalarProgram.scalarStacks, StackRoutines.copyStacks]
  rw [hfinal] at he
  have hlen : (d.stacks 19).length = width p := by simp [d, operands, wide]
  simpa only [copy, hlen] using he

theorem copy_zero_eval (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (a c left : List Bool) :
    Eval (copy 14 1) (7 * width p + 5)
      (operands p regs g neg ok xs a c left [])
      (operands p (readRegs regs 0 1 none) g neg ok xs a c left (word p 0)) := by
  let d := operands p regs g neg ok xs a c left []
  have he := SubexpScanPrimitives.copy_eval d 14 1 9 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simp [d, operands, wide, MatrixScalarProgram.scalarStacks])
  have hfinal : afterCopy d 14 1 0 1 =
      operands p (readRegs regs 0 1 none) g neg ok xs a c left (word p 0) := by
    apply state_ext
    · funext j
      fin_cases j <;> simp [d, operands, wide, afterCopy, readRegs]
    · funext j
      fin_cases j <;> simp [d, operands, wide, afterCopy,
        MatrixScalarProgram.scalarStacks, StackRoutines.copyStacks]
  rw [hfinal] at he
  have hlen : (d.stacks 14).length = width p := by
    simp [d, operands, wide, MatrixScalarProgram.scalarStacks]
  simpa only [copy, hlen] using he

/-- Negative parity is implemented by one actual modular addition. -/
theorem prepareComparison_eval (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (a c : List Bool) (x : ZMod p) :
    ∃ n ≤ 6000 * (width p + 1)^2 + 14 * width p + 12, ∃ regs',
      Eval prepareComparison n (operands p regs g neg ok xs a c (word p x) [])
        (operands p regs' g neg ok xs a c
          (word p (leftAdjusted p neg x)) (word p (rightConstant p neg))) := by
  cases neg with
  | false =>
      have he := copy_one_eval p regs g false ok xs a c (word p x)
      refine ⟨7 * width p + 5 + 1, by omega, readRegs regs 0 1 none, ?_⟩
      apply Eval.ite_false
      · simp [operands, wide]
      · exact he
  | true =>
      have h₁ := copy_one_eval p regs g true ok xs a c (word p x)
      obtain ⟨n, hn, r, h₂⟩ := scalarAdd_eval p (readRegs regs 0 1 none) g true ok xs a c x 1
      have h₃ := copy_zero_eval p r g true ok xs a c (word p (x + 1))
      have he := h₁.seq (h₂.seq h₃)
      refine ⟨(7 * width p + 5 + (n + (7 * width p + 5))) + 1, by omega,
        readRegs r 0 1 none, ?_⟩
      apply Eval.ite_true
      · simp [operands, wide]
      · exact he


/-- Loading a head parses a real framed word and reverses the parser's
scratch output. The saved vector itself is retained. -/
theorem loadHead_eval (regs : Fin 8 → Bool) (g neg ok : Bool)
    (x : ZMod p) (rest : List (ZMod p)) (a c : List Bool) :
    ∃ n ≤ 9 * ((x :: rest).length * (2 * width p + 1)) + 9 * width p + 15,
      ∃ regs', Eval loadHead n (ready p regs g neg ok (x :: rest) a c)
        (operands p regs' g neg ok (x :: rest) a c (word p x) []) := by
  let xs := x :: rest
  let d₀ := ready p regs g neg ok xs a c
  let d₁ := afterCopy d₀ 12 10 0 1
  let L := xs.length * (2 * width p + 1)
  let tail := CoefficientPascalProgram.valueWords p rest
  have hL : (CoefficientPascalProgram.valueWords p xs).length = L :=
    CoefficientPascalProgram.valueWords_length p xs
  have h₁ : Eval (copy 12 10) (7 * L + 5) d₀ d₁ := by
    have he := SubexpScanPrimitives.copy_eval d₀ 12 10 9 0 1
      (by decide) (by decide) (by decide) (by decide)
      (by simp [d₀, ready, wide, lowData, MatrixScalarProgram.state, MatrixScalarProgram.scalarStacks])
    have hlen : (d₀.stacks 12).length = L := by
      simpa [d₀, ready, wide, lowData, MatrixScalarProgram.state,
        MatrixScalarProgram.scalarStacks] using hL
    simpa only [copy, hlen] using he
  let d₂ := RecordPrograms.state wordPorts d₁ false true (d₁.regs 2)
    tail (word p x).reverse
  have hentry : RecordPrograms.state wordPorts d₁ (d₁.regs 0) (d₁.regs 1) (d₁.regs 2)
      (Encoding.frame (word p x) ++ tail) [] = d₁ := by
    apply state_ext
    · funext j
      fin_cases j <;> simp [RecordPrograms.state, wordPorts]
    · funext j
      fin_cases j <;> simp [RecordPrograms.state, wordPorts, d₁, afterCopy,
        StackRoutines.copyStacks, d₀, ready, wide, lowData, MatrixScalarProgram.state,
        MatrixScalarProgram.scalarStacks, xs, tail, CoefficientPascalProgram.valueWords,
        MatrixProgramSupport.words]
  have h₂ : Eval (RecordPrograms.reader wordPorts) (6 * width p + 4) d₁ d₂ := by
    have he := RecordPrograms.reader_eval wordPorts d₁ (word p x) tail []
      (d₁.regs 0) (d₁.regs 1) (d₁.regs 2)
    rw [hentry] at he
    simpa only [word_length, List.append_nil] using he
  let d₃ := afterTransfer d₂ 9 0 0 1
  have h₃ : Eval (transfer 9 0) (3 * width p + 3) d₂ d₃ := by
    have hlen : (d₂.stacks 9).length = width p := by
      simp [d₂, RecordPrograms.state, wordPorts]
    simpa only [transfer, hlen] using
      SubexpScanPrimitives.transfer_eval d₂ 9 0 0 1 (by decide) (by decide)
  let d₄ := cleared d₃ 10
  have h₄ : Eval (clear 10) (2 * tail.length + 3) d₃ d₄ := by
    have hlen : (d₃.stacks 10).length = tail.length := by
      simp [d₃, afterTransfer, StackRoutines.transferStacks, d₂, RecordPrograms.state, wordPorts]
    simpa only [hlen] using clear_eval d₃ 10
  let r := readRegs regs 0 1 none
  have hfinal : d₄ = operands p r g neg ok xs a c (word p x) [] := by
    apply state_ext
    · funext j
      fin_cases j <;> simp [d₄, cleared, d₃, afterTransfer, d₂, RecordPrograms.state,
        wordPorts, d₁, afterCopy, d₀, ready, lowData, operands, wide,
        MatrixScalarProgram.state, readRegs, r]
    · funext j
      fin_cases j <;> simp [d₄, cleared, d₃, afterTransfer, d₂, RecordPrograms.state,
        wordPorts, d₁, afterCopy, d₀, ready, lowData, operands, wide,
        MatrixScalarProgram.state, MatrixScalarProgram.scalarStacks,
        StackRoutines.transferStacks, StackRoutines.copyStacks]
  have he := h₁.seq (h₂.seq (h₃.seq h₄))
  rw [hfinal] at he
  refine ⟨(7 * L + 5) + ((6 * width p + 4) + ((3 * width p + 3) +
    (2 * tail.length + 3))), ?_, r, he⟩
  have htail : tail.length ≤ L := by
    simp [tail, CoefficientPascalProgram.valueWords_length, L, xs]
  change _ ≤ 9 * L + 9 * width p + 15
  omega

/-- The comparison's five local registers are framed by the remaining
registers of the scalar service. -/
def withFive (r : Fin 5 → Bool) (base : Fin 8 → Bool) : Fin 8 → Bool :=
  Fin.addCases (m := 5) (n := 3) (motive := fun _ => Bool)
    r (fun i : Fin 3 => base (Fin.natAdd 5 i))

/-- Actual bitwise equality followed by physical cleanup and conjunction
with the accumulated answer. The statement does not assume a clean equality
endpoint: both residual operand stacks are cleared here. -/
theorem equalityClean_eval (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (a c : List Bool) (x y : ZMod p) :
    ∃ n ≤ 13 * width p + 16, ∃ regs',
      Eval (.seq equality (.seq (clear 0) (.seq (clear 1)
        (.base (.atom (.band 10 10 4)))))) n
        (operands p regs g neg ok xs a c (word p x) (word p y))
        (ready p regs' g neg (ok && decide (x = y)) xs a c) := by
  let d₀ := operands p regs g neg ok xs a c (word p x) (word p y)
  let small := fun i : Fin 5 => regs (Fin.castAdd 3 i)
  obtain ⟨endCfg, ⟨n, hn, ht⟩, hpc, hout, hleft, hright⟩ :=
    ExecClauseCost.bitEquality_runsIn_bounded small (word p x) (word p y)
  let localEnd : State 5 2 := ⟨endCfg.regs, endCfg.stacks⟩
  let r₁ := withFive endCfg.regs regs
  let d₁ := operands p r₁ g neg ok xs a c (endCfg.stacks 0) (endCfg.stacks 1)
  have hproj : projectState equalityRegisters equalityStacks d₀ =
      ⟨small, ExecClauseCost.bitStacks (word p x) (word p y)⟩ := by
    apply state_ext
    · funext j
      fin_cases j <;> rfl
    · funext j
      fin_cases j <;> rfl
  have hend : localEnd.withPC none = endCfg := by
    cases endCfg
    simp_all [localEnd, StructuredProgram.State.withPC]
  have htrace : Trace ExecClauseCost.bitEqualityProgram n
      ((projectState equalityRegisters equalityStacks d₀).withPC
        (some ExecClauseCost.bitEqualityProgram.entry)) (localEnd.withPC none) := by
    rw [hproj, hend]
    exact ht
  have hembed : embedState equalityRegisters equalityStacks d₀ localEnd = d₁ := by
    apply embedState_eq equalityRegisters equalityStacks equalityRegisters_injective
      equalityStacks_injective
    · intro i
      fin_cases i <;> simp [d₁, r₁, withFive, operands, wide, localEnd, equalityRegisters]
    · intro i
      fin_cases i <;> simp [d₁, operands, wide,
        MatrixScalarProgram.scalarStacks, localEnd, equalityStacks]
    · intro j hj
      revert hj
      refine Fin.addCases (m := 5) (n := 6) (fun i => ?_) (fun i => ?_) j
      · intro hi
        exact (hi ⟨i,rfl⟩).elim
      · intro _
        fin_cases i <;> rfl
    · intro j hj
      have h0 : j ≠ 0 := by intro h; subst j; exact hj ⟨0,rfl⟩
      have h1 : j ≠ 1 := by intro h; subst j; exact hj ⟨1,rfl⟩
      change (operands p r₁ g neg ok xs a c (endCfg.stacks 0) (endCfg.stacks 1)).stacks j =
        (operands p regs g neg ok xs a c (word p x) (word p y)).stacks j
      rw [operands_stack,operands_stack]
      simp only [ite_eq_right h0,ite_eq_right h1]
      rfl
  have h₁ : Eval equality n d₀ d₁ := by
    have he := eval_call_from_state ExecClauseCost.bitEqualityProgram
      equalityRegisters equalityStacks d₀ equalityRegisters_injective equalityStacks_injective htrace
    rw [hembed] at he
    exact he
  let d₂ := cleared d₁ 0
  let d₃ := cleared d₂ 1
  have h₂ : Eval (clear 0) (2 * (endCfg.stacks 0).length + 3) d₁ d₂ := by
    have hlen : (d₁.stacks 0).length = (endCfg.stacks 0).length := by
      simp [d₁, operands, wide, MatrixScalarProgram.scalarStacks]
    simpa only [hlen] using clear_eval d₁ 0
  have h₃ : Eval (clear 1) (2 * (endCfg.stacks 1).length + 3) d₂ d₃ := by
    have hlen : (d₂.stacks 1).length = (endCfg.stacks 1).length := by
      simp [d₂, cleared, d₁, operands, wide, MatrixScalarProgram.scalarStacks]
    simpa only [hlen] using clear_eval d₂ 1
  let r₃ := readRegs r₁ 0 1 none
  have hwords : decide (word p x = word p y) = decide (x = y) := by
    exact Bool.decide_congr (word_injective p).eq_iff
  have hband : (StructuredProgram.Atom.band 10 10 4).eval d₃ =
      ready p r₃ g neg (ok && decide (x = y)) xs a c := by
    apply state_ext
    · funext j
      fin_cases j <;> simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        d₃, d₂, cleared, d₁, operands, ready, lowData, wide, MatrixScalarProgram.state,
        r₃, r₁, withFive, readRegs, hout, hwords]
    · funext j
      fin_cases j <;> simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        d₃, d₂, cleared, d₁, operands, ready, lowData, wide, MatrixScalarProgram.state,
        MatrixScalarProgram.scalarStacks]
  have h₄ : Eval (.base (.atom (.band 10 10 4))) 1 d₃
      (ready p r₃ g neg (ok && decide (x = y)) xs a c) := by
    rw [← hband]
    exact .base (.atom _ _)
  refine ⟨n + ((2 * (endCfg.stacks 0).length + 3) +
      ((2 * (endCfg.stacks 1).length + 3) + 1)), ?_, r₃, h₁.seq (h₂.seq (h₃.seq h₄))⟩
  simp only [word_length] at hn hleft hright
  omega

def compareBudget (R B : ℕ) : ℕ := 6000 * (B + 1)^2 + 10 * R * (2 * B + 1) + 40 * B + 50

/-- A full head test has a real finite-machine derivation and updates the
answer with precisely the signed field equation. -/
theorem compareHead_eval (regs : Fin 8 → Bool) (g neg ok : Bool)
    (x : ZMod p) (rest : List (ZMod p)) (a c : List Bool) :
    ∃ n ≤ compareBudget (x :: rest).length (width p), ∃ regs',
      Eval compareHead n (ready p regs g neg ok (x :: rest) a c)
        (ready p regs' g neg
          (ok && decide (x = CoefficientCheckerSemantics.sign neg)) (x :: rest) a c) := by
  obtain ⟨n₁, h₁, r₁, e₁⟩ := loadHead_eval p regs g neg ok x rest a c
  obtain ⟨n₂, h₂, r₂, e₂⟩ := prepareComparison_eval p r₁ g neg ok (x :: rest) a c x
  obtain ⟨n₃, h₃, r₃, e₃⟩ := equalityClean_eval p r₂ g neg ok (x :: rest) a c
    (leftAdjusted p neg x) (rightConstant p neg)
  have he := e₁.seq (e₂.seq e₃)
  have htest : decide (leftAdjusted p neg x = rightConstant p neg) =
      decide (x = CoefficientCheckerSemantics.sign neg) := by
    exact Bool.decide_congr (adjusted_eq_iff p neg x)
  rw [htest] at he
  refine ⟨n₁ + (n₂ + n₃), ?_, r₃, he⟩
  dsimp [compareBudget]
  simp only [List.length_cons, Nat.mul_assoc] at h₁ h₂ h₃ ⊢
  omega

end SubexponentialSAT.Subexp.CoefficientCheckerProgram

end OAI.Algorithms
