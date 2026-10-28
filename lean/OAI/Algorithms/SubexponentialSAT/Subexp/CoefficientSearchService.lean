import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearchSetup
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearchExecution
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchArithmetic
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientNormalization

namespace OAI.Algorithms

/-! The closed normalized-coefficient service builds its own scalar alphabet,
generates its candidates, and returns the first successful encoded vector. -/

namespace SubexponentialSAT.Subexp.CoefficientSearchService

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

open BitProgram StructuredCalls

abbrev command : Cmd 14 32 :=
  .seq CoefficientSearchSetup.setup CoefficientSearchProgram.command

def program := compiled command 14 21

variable (p : ℕ) [Fact p.Prime]

def budget (A R : ℕ) : ℕ := ScalarSetupProgram.budget p +
  2 * (ProgramEncoding.encodeRecords (ScalarSetupProgram.rawAlphabet p)).length + 3 +
  CoefficientSearchProgram.searchBudget p A R

/-- A fixed-degree polynomial multiplies the actual p^R candidate count.
The scalar alphabet construction is included, also when R=0. -/
theorem budget_le (A R : ℕ) :
    budget p A R ≤ 2000000 * (p + 1) * (A + R + 1) * (R + 1) *
      (MatrixWordEncoding.width p + 1)^2 * p^R := by
  let B := MatrixWordEncoding.width p
  let K := (A + R + 1) * (R + 1) * (B + 1)^2
  let G := (p + 1) * K * p^R
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hpow : 1 ≤ p^R := Nat.one_le_pow _ _ hp
  have hB : B + 1 ≤ K := by
    calc
      B + 1 ≤ (B + 1)^2 := by nlinarith
      _ = 1 * 1 * (B + 1)^2 := by ring
      _ ≤ K := Nat.mul_le_mul_right _
        (Nat.mul_le_mul (by omega : 1 ≤ A + R + 1) (by omega : 1 ≤ R + 1))
  have hBP : B + 1 ≤ K * p^R := by
    calc
      _ ≤ K := hB
      _ = K * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hpow
  have hsetup : CoefficientSearchSetup.budget p ≤ 200 * G := by
    calc
      _ ≤ 200 * (p + 1) * (B + 1) := CoefficientSearchSetup.budget_le p
      _ ≤ 200 * (p + 1) * (K * p^R) := Nat.mul_le_mul_left _ hBP
      _ = _ := by dsimp [G]; ring
  have hcore : CoefficientSearchProgram.searchBudget p A R ≤ 1000000 * G := by
    calc
      _ ≤ 1000000 * K * p^R := by
        simpa only [K, B, Nat.mul_assoc] using CoefficientSearchProgram.searchBudget_le p A R
      _ = 1000000 * (1 * K * p^R) := by ring
      _ ≤ 1000000 * ((p + 1) * K * p^R) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right _ (by omega : 1 ≤ p + 1)))
      _ = _ := by rfl
  change CoefficientSearchSetup.budget p + CoefficientSearchProgram.searchBudget p A R ≤ _
  have hsum := Nat.add_le_add hsetup hcore
  calc
    _ ≤ 200 * G + 1000000 * G := hsum
    _ ≤ 2000000 * G := by omega
    _ = _ := by dsimp [G,K,B]; ring

/-- Only local universal-block parameters occur in this search exponent.
The bound applies to the actual service budget, including alphabet setup. -/
theorem budget_le_local_exponential (A R U : ℕ) (hpU : p ≤ U)
    (hA : A ≤ U) (hR : R ≤ U) (hB : MatrixWordEncoding.width p ≤ U) :
    budget p A R ≤ 2 ^ (2000000 * (U + 1)^10) := by
  let X := U + 1
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hAR : A + R + 1 ≤ 2 * X := by dsimp [X]; omega
  have hp1 : p + 1 ≤ X := Nat.add_le_add_right hpU 1
  have hR1 : R + 1 ≤ X := Nat.add_le_add_right hR 1
  have hB1 : MatrixWordEncoding.width p + 1 ≤ X := Nat.add_le_add_right hB 1
  have hpower : p^R ≤ p^(U*U+U) := Nat.pow_le_pow_right hp (by omega)
  have h58 : X^5 ≤ X^8 := Nat.pow_le_pow_right hX (by decide)
  have hmajor : budget p A R ≤ 4 * (1000000 * X^8 * p^(U*U+U)) := by
    calc
      _ ≤ 2000000 * (p + 1) * (A + R + 1) * (R + 1) *
          (MatrixWordEncoding.width p + 1)^2 * p^R := budget_le p A R
      _ ≤ 2000000 * X * (2 * X) * X * X^2 * p^(U*U+U) := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hp1) hAR) hR1)
            (Nat.pow_le_pow_left hB1 2)) hpower
      _ = 4000000 * X^5 * p^(U*U+U) := by ring
      _ ≤ 4000000 * X^8 * p^(U*U+U) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h58)
      _ = _ := by ring
  have hsearch := BlockSearchArithmetic.polynomial_times_search_le_two_pow p U hpU
  have hone : 1 ≤ X^10 := by simpa using Nat.pow_le_pow_left hX 10
  calc
    _ ≤ 4 * (1000000 * X^8 * p^(U*U+U)) := hmajor
    _ ≤ 4 * 2^(1000000 * X^10) := Nat.mul_le_mul_left 4 hsearch
    _ = 2^(2 + 1000000 * X^10) := by rw [pow_add]; rfl
    _ ≤ 2^(2000000 * X^10) := Nat.pow_le_pow_right (by decide) (by omega)

/-- The service accepts only a prime word and unary interval parameters.
No scalar alphabet, candidate list, or successful coefficient tuple is part
of its input. Every phase is an actual fixed-program execution. -/
theorem command_eval (h2 : (2 : ZMod p) ≠ 0) (A R : ℕ) (regs : Fin 14 → Bool) :
    ∃ (n : ℕ) (final : State 14 32) (v : Fin R → ZMod p), n + 1 ≤ budget p A R ∧
      Eval command n (CoefficientSearchSetup.rawInput p A R regs) final ∧
      CoefficientSearchProgram.Invariant p A R
        (ProgramEncoding.encodeRecords (CoefficientSearchSemantics.scalarTokens p)) final ∧
      final.stacks 21 = CoefficientSearchSemantics.encode p v ∧
      (∀ d < R, CoefficientDynamics.evaluate (List.ofFn v) (A + d) = (-1 : ZMod p)^(A + d)) := by
  obtain ⟨ns,hs,r,es⟩ := CoefficientSearchSetup.setup_eval p A R regs
  obtain ⟨nc,final,v,hc,ec,hi,hout,hv⟩ := CoefficientSearchProgram.command_eval p h2 A R r
    (regs 8) (regs 9) (regs 10) false false (regs 13)
  refine ⟨ns + nc,final,v,?_,es.seq ec,hi,hout,hv⟩
  change ns ≤ ScalarSetupProgram.budget p +
    2 * (ProgramEncoding.encodeRecords (ScalarSetupProgram.rawAlphabet p)).length + 3 at hs
  dsimp [budget]
  omega

theorem program_run (h2 : (2 : ZMod p) ≠ 0) (A R : ℕ) (regs : Fin 14 → Bool) :
    ∃ (final : State 14 32) (v : Fin R → ZMod p),
      RunsIn program (budget p A R)
        ((CoefficientSearchSetup.rawInput p A R regs).withPC (some program.entry))
        (final.withPC none) ∧
      final.stacks 21 = CoefficientSearchSemantics.encode p v ∧
      (∀ d < R, CoefficientDynamics.evaluate (List.ofFn v) (A + d) = (-1 : ZMod p)^(A + d)) := by
  obtain ⟨n,final,v,hn,he,_,hout,hv⟩ := command_eval p h2 A R regs
  exact ⟨final,v,⟨n + 1,hn,compiled_halt_trace he 14 21⟩,hout,hv⟩

/-- The bytes remain normalized. Their mathematical unnormalization is the
unique coefficient function used by the matrix-entry recurrence. -/
theorem program_coefficients (h2 : (2 : ZMod p) ≠ 0) (A R : ℕ) (regs : Fin 14 → Bool) :
    ∃ (final : State 14 32) (v : Fin R → ZMod p),
      RunsIn program (budget p A R)
        ((CoefficientSearchSetup.rawInput p A R regs).withPC (some program.entry))
        (final.withPC none) ∧
      final.stacks 21 = CoefficientSearchSemantics.encode p v ∧
      CoefficientNormalization.unnormalize (List.ofFn v) =
        CoefficientSearch.coefficientsNat p A R := by
  obtain ⟨final,v,hr,hout,hv⟩ := program_run p h2 A R regs
  refine ⟨final,v,hr,hout,?_⟩
  apply CoefficientNormalization.coefficients_eq p A R (Fact.out : p.Prime).pos
    (List.ofFn v) (by simp)
  intro d
  exact hv d.val d.isLt

theorem primitive_run (h2 : (2 : ZMod p) ≠ 0) (A R : ℕ) (regs : Fin 14 → Bool) :
    ∃ (final : State 14 32) (v : Fin R → ZMod p),
      Computation.RunsIn (primitive program).step (primitiveOverhead program * budget p A R)
        (primitiveCfg program ((CoefficientSearchSetup.rawInput p A R regs).withPC (some program.entry)))
        (primitiveCfg program (final.withPC none)) ∧
      final.stacks 21 = CoefficientSearchSemantics.encode p v ∧
      (∀ d < R, CoefficientDynamics.evaluate (List.ofFn v) (A + d) = (-1 : ZMod p)^(A + d)) := by
  obtain ⟨final,v,he,hout,hv⟩ := program_run p h2 A R regs
  exact ⟨final,v,primitive_execution program he,hout,hv⟩

end SubexponentialSAT.Subexp.CoefficientSearchService

end OAI.Algorithms
