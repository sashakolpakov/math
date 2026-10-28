import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTAtZero
import OAI.Algorithms.SubexponentialSAT.SubexpCountExtraction
import OAI.Algorithms.SubexponentialSAT.SubexpMainDecode

namespace OAI.Algorithms

/-!
# Decode the single quartet returned by reconstruction at zero

The concrete CRT implementation returns H(0), so its output is one quartet.
No equality to a full reconstructed coefficient list is needed. The preceding
CRT trace must still establish the returned quartet's stated denotation.
-/

namespace SubexponentialSAT.SubexpH0CountDecision

open BitProgram StructuredCalls SubexpMainProgram SubexpQuarticRing SubexpLayoutSpec

def budget (B : ℕ) : ℕ := 16 * (5 * B + 1) + 420 * (B + 1)^2 + 1

theorem singleton_budget_le {B : ℕ} (output : SubexpFlatCount.Code B)
    (modulus : List Bool) (hm : modulus.length ≤ B + 1) :
    SubexpFlatCount.budget B modulus (SubexpFlatCount.flatPolynomial [output]) ≤ budget B := by
  have hf : (SubexpFlatCount.flatPolynomial [output]).length = 4 * B := by
    simp [SubexpFlatCount.flatPolynomial_length]
  have hm' : modulus.length + B + 1 ≤ 2 * (B + 1) := by omega
  have hd : 105 * (modulus.length + B + 1)^2 ≤ 420 * (B + 1)^2 := by
    calc
      _ ≤ 105 * (2 * (B + 1))^2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm' 2)
      _ = _ := by ring
  unfold SubexpFlatCount.budget budget
  rw [hf]
  nlinarith

variable {p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  (S : Factor.System V F (ZMod p)) {c : Parameters p k Δ r tau}
  (L : Layout (E := SubexpActualRing.E p) S.toPattern c)

local notation "D" => Fintype.card V
local notation "B" => SubexpLiftRing.baseWidth p (D + 1)
local notation "coeffs" => QuarticSearch.liftedCoefficients p (D + 1)

omit [DecidableEq F] in
/-- The modulo word is derived from the selected reconstruction at zero.
The actual CRT producer supplies `computed`, not a count oracle. -/
theorem firstWord_mod (output : SubexpFlatCount.Code B) (hD : 0 < D)
    (computed : SubexpHornerMachine.decode p (D + 1) coeffs output =
      SubexpCRTAtZero.selectedValue S L) :
    BinaryArithmetic.toNat output.c0.val % p^(D + 1) = Factor.count S := by
  apply SubexpDecodedCount.first_mod_eq p (D + 1) (Nat.succ_pos D) coeffs output
    (Factor.count S) (Counting.factor_count_lt_prime_power S)
  exact computed.trans (SubexpCRTAtZero.selectedValue_eq_count S L hD)

omit [DecidableEq F] in
theorem answer_iff (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (output : SubexpFlatCount.Code B) (hD : 0 < D)
    (computed : SubexpHornerMachine.decode p (D + 1) coeffs output =
      SubexpCRTAtZero.selectedValue S L) :
    SubexpDecodeProgram.answer M.bits output.c0.val = true ↔
      ∃ x : V → ZMod p, Factor.Satisfies S x := by
  have hm : 0 < BinaryArithmetic.toNat M.bits := by
    rw [M.value]
    exact pow_pos (Fact.out : p.Prime).pos _
  rw [SubexpDecodeProgram.answer_iff _ _ hm, M.value, firstWord_mod S L output hD computed]
  exact Factor.count_pos_iff S

omit [DecidableEq F] in
/-- Physical main-state execution on the singleton output. Other persistent
fields are framed; the cost is quadratic in the represented word width. -/
theorem main_execution {er es : ℕ}
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (output : SubexpFlatCount.Code B) (hD : 0 < D)
    (computed : SubexpHornerMachine.decode p (D + 1) coeffs output =
      SubexpCRTAtZero.selectedValue S L)
    (a : MainState er es) (regs : Fin 8 → Bool) (width : List Bool)
    (hwidth : width.length = B)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start regs M.bits width (SubexpFlatCount.flatPolynomial [output])) :
    ∃ (n : ℕ) (final : MainState er es),
      n ≤ budget B ∧
      Eval (SubexpMainDecode.procedure er es).invoke n a final ∧
      ((final.stacks (persistent es 10)).head? = some true ↔
        ∃ x : V → ZMod p, Factor.Satisfies S x) ∧
      (∀ j : Fin 32, j ≠ 10 → j ≠ 12 → j ≠ 13 →
        final.stacks (persistent es j) = a.stacks (persistent es j)) := by
  have hB : 0 < B := by unfold SubexpLiftRing.baseWidth; positivity
  obtain ⟨n, finalRegs, hn, heval⟩ :=
    SubexpMainDecode.execution hB [output] a regs M.bits width hwidth ready
  refine ⟨n, _, hn.trans (singleton_budget_le output M.bits M.length_le), heval, ?_, ?_⟩
  · rw [SubexpMainDecode.installed_head, Option.some.injEq]
    exact answer_iff S L M output hD computed
  · intro j h10 h12 h13
    exact SubexpMainDecode.installed_frame a _ j h10 h12 h13

omit [DecidableEq F] in
/-- The standalone finite decoder also has a primitive-machine trace on the
single quartet; earlier reconstruction work is excluded from this bound. -/
theorem primitive_execution
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (output : SubexpFlatCount.Code B) (hD : 0 < D)
    (computed : SubexpHornerMachine.decode p (D + 1) coeffs output =
      SubexpCRTAtZero.selectedValue S L)
    (regs : Fin 8 → Bool) (width : List Bool) (hwidth : width.length = B) :
    ∃ final : (primitive SubexpFlatCount.program).Cfg,
      Computation.RunsIn (primitive SubexpFlatCount.program).step
        (primitiveOverhead SubexpFlatCount.program * budget B)
        (primitiveCfg SubexpFlatCount.program
          ((SubexpFlatCount.start regs M.bits width
            (SubexpFlatCount.flatPolynomial [output])).withPC
              (some SubexpFlatCount.program.entry))) final ∧
      (final.state = .inl true ↔ ∃ x : V → ZMod p, Factor.Satisfies S x) := by
  have hB : 0 < B := by unfold SubexpLiftRing.baseWidth; positivity
  obtain ⟨finalRegs, hrun⟩ := SubexpFlatCount.primitive_run hB [output] regs M.bits width hwidth
  refine ⟨_, hrun.mono (Nat.mul_le_mul_left _
    (singleton_budget_le output M.bits M.length_le)), ?_⟩
  have ha : (primitiveCfg SubexpFlatCount.program
      ⟨none, finalRegs, SubexpFlatCount.store
        (SubexpFlatCount.output M.bits output.c0.val) M.bits [] width⟩).state =
      .inl (SubexpDecodeProgram.answer M.bits output.c0.val) := by
    apply StackCompiler.compiled_terminal
    rfl
  change (primitiveCfg SubexpFlatCount.program
      ⟨none, finalRegs, SubexpFlatCount.store
        (SubexpFlatCount.output M.bits output.c0.val) M.bits [] width⟩).state = .inl true ↔ _
  rw [ha, Sum.inl.injEq]
  exact answer_iff S L M output hD computed

end SubexponentialSAT.SubexpH0CountDecision

end OAI.Algorithms
