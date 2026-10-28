import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchExecution
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchInputBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixBudgetBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchCostEnvelope

namespace OAI.Algorithms

/-!
# A concrete exponential bound for the actual local-basis batch

The canonical master words, actual Side dimensions, matrix construction,
finite search, and outer-loop serialization are all charged. The hypotheses
bound numeric input parameters and the physically enumerated universal type
count; no per-color execution or output-size bound is supplied by the caller.
-/

namespace SubexponentialSAT.Subexp.LocalBasisBatchBounds

open BitProgram LocalBasisBatchProgram

variable {r Q Δ : ℕ}

theorem columns_length_le (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)
    (U : ℕ) (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    (ConstraintMatrixProgram.columns (Δ := Δ) hr hQ t g).length ≤ U := by
  simpa only [ConstraintMatrixProgram.columns, List.length_map] using
    sideList_length_le hr hQ t g U hu

theorem rowList_length_le (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)
    (U : ℕ) (hΔU : Δ ≤ U) (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    (ConstraintMatrixProgram.rowList (Δ := Δ) hr hQ t g).length ≤ U^2 := by
  rw [ConstraintMatrixProgram.rowList_length]
  calc
    _ ≤ Δ * (ConstraintMatrixProgram.columns (Δ := Δ) hr hQ t g).length :=
      ConstraintMatrixProgram.rowCount_le_slots_columns hr hQ t g
    _ ≤ U * U := Nat.mul_le_mul hΔU (columns_length_le hr hQ t g U hu)
    _ = U^2 := by ring

/-- The batch's concrete entry allowance is transported to the proved
one-Side cap at `5*U`; it is not silently replaced by a smaller allowance. -/
theorem matrixBudget_le (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (coefficients : List (ZMod p)) (t : Fin Q) (g : Fin r) (U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hR : coefficients.length ≤ U) (hw : MatrixWordEncoding.width p ≤ U)
    (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    ConstraintMatrixProgram.budget (Δ := Δ) p hr hQ t g coefficients
      (LocalBasisBatchProgram.entryCap p r Q Δ coefficients.length) ≤
        4000000000000 * (U + 1)^8 := by
  have hU5 : U ≤ 5 * U := by omega
  have hE : LocalBasisBatchProgram.entryCap p r Q Δ coefficients.length ≤
      ConstraintMatrixBudgetBounds.entryCap (5 * U) := by
    unfold LocalBasisBatchProgram.entryCap LocalBasisBatchProgram.entryExtent
      ConstraintMatrixBudgetBounds.entryCap
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  have hm := ConstraintMatrixBudgetBounds.budget_le_of_entryCap p hr hQ t g coefficients
    (LocalBasisBatchProgram.entryCap p r Q Δ coefficients.length) (5 * U)
    (hrU.trans hU5) (hQU.trans hU5) (hΔU.trans hU5) (hw.trans hU5)
    ((columns_length_le hr hQ t g U hu).trans hU5) hE
  calc
    _ ≤ 10000000 * (5 * U + 1)^8 := hm
    _ ≤ 10000000 * (5 * (U + 1))^8 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 8)
    _ = 3906250000000 * (U + 1)^8 := by ring
    _ ≤ 4000000000000 * (U + 1)^8 := Nat.mul_le_mul_right _ (by decide)

theorem searchBudget_le (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (alphabet : List (ZMod p)) (hcard : alphabet.length = p)
    (t : Fin Q) (g : Fin r) (U : ℕ)
    (hΔU : Δ ≤ U) (hp : p ≤ U) (hw : MatrixWordEncoding.width p ≤ U)
    (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    BlockSearchExecution.cost (BlockSearchPredicate.scalarCode p) alphabet
      (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length
      (BlockCoefficientProgram.coefficientCost p
        (ConstraintMatrixProgram.rowList (Δ := Δ) hr hQ t g).length
        (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length) ≤
          2 ^ (1000000 * (U + 1)^10) :=
  BlockSearchCostEnvelope.cost_le_two_pow p alphabet hcard _ _ U hp
    (sideList_length_le hr hQ t g U hu) (rowList_length_le hr hQ t g U hΔU hu) hw

private theorem point_envelope (D F M S A B : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hD : D ≤ 2000 * A) (hF : F ≤ 40 * A) (hM : M ≤ 4000000000000 * A)
    (hS : S ≤ B) :
    D + 1000000000 * (F + M + S + 1) ≤ 100000000000000000000000 * A * B := by
  have hAB : A ≤ A * B := by simpa only [mul_one] using Nat.mul_le_mul_left A hB
  have hBA : B ≤ A * B := by simpa only [one_mul] using Nat.mul_le_mul_right B hA
  nlinarith only [hA, hB, hD, hF, hM, hS, hAB, hBA]

theorem colorPointBudget_le (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (coefficients alphabet : List (ZMod p)) (hcard : alphabet.length = p)
    (t : Fin Q) (g : Fin r) (U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hR : coefficients.length ≤ U) (hp : p ≤ U) (hw : MatrixWordEncoding.width p ≤ U)
    (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    LocalBasisBatchProgram.colorPointBudget (Δ := Δ) p hr hQ coefficients alphabet t g ≤
      100000000000000000000000 * (U + 1)^8 * 2 ^ (1000000 * (U + 1)^10) := by
  have hA : 1 ≤ (U + 1)^8 := Nat.one_le_pow _ _ (by omega)
  have hB : 1 ≤ 2 ^ (1000000 * (U + 1)^10) := Nat.one_le_pow _ _ (by decide)
  have h48 : (U + 1)^4 ≤ (U + 1)^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hD := sideDimensionsCost_le hr hQ t g U hrU hQU hΔU hu
  have hF := (colorExtent_le p hr hQ coefficients alphabet hcard t g U
    hrU hQU hΔU hR hp hw hu).trans (Nat.mul_le_mul_left 40 h48)
  have hM := matrixBudget_le p hr hQ coefficients t g U hrU hQU hΔU hR hw hu
  have hS := searchBudget_le p hr hQ alphabet hcard t g U hΔU hp hw hu
  exact point_envelope _ _ _ _ _ _ hA hB hD hF hM hS

theorem colorBudget_le (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (coefficients alphabet : List (ZMod p)) (hcard : alphabet.length = p) (U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hR : coefficients.length ≤ U) (hp : p ≤ U) (hw : MatrixWordEncoding.width p ≤ U)
    (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    LocalBasisBatchProgram.colorBudget (Δ := Δ) p hr hQ coefficients alphabet ≤
      100000000000000000000000 * (U + 1)^8 * 2 ^ (1000000 * (U + 1)^10) := by
  unfold LocalBasisBatchProgram.colorBudget
  apply Finset.sup_le
  intro t _
  apply Finset.sup_le
  intro g _
  exact colorPointBudget_le p hr hQ coefficients alphabet hcard t g U
    hrU hQU hΔU hR hp hw hu

theorem loop_envelope (r Q C : ℕ) :
    widthCost r Q + coreCost r Q C + 1 ≤ 1000 * (r + 1) * (Q + 1) * (C + 1) := by
  unfold widthCost coreCost positionLoopCost positionCost colorLoopCost
  ring_nf
  omega

theorem sourceBudget_le_polynomial_times_search (p : ℕ) [Fact p.Prime]
    (hr : 0 < r) (hQ : 0 < Q)
    (coefficients alphabet : List (ZMod p)) (hcard : alphabet.length = p) (U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hR : coefficients.length ≤ U) (hp : p ≤ U) (hw : MatrixWordEncoding.width p ≤ U)
    (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    sourceBudget (Δ := Δ) p hr hQ coefficients alphabet ≤
      1000000000000000000000000000 * (U + 1)^10 * 2 ^ (1000000 * (U + 1)^10) := by
  let C := LocalBasisBatchProgram.colorBudget (Δ := Δ) p hr hQ coefficients alphabet
  let B := 2 ^ (1000000 * (U + 1)^10)
  have hA : 1 ≤ (U + 1)^8 := Nat.one_le_pow _ _ (by omega)
  have hB : 1 ≤ B := Nat.one_le_pow _ _ (by decide)
  have hc : C ≤ 100000000000000000000000 * (U + 1)^8 * B :=
    colorBudget_le p hr hQ coefficients alphabet hcard U hrU hQU hΔU hR hp hw hu
  have hpositive : 1 ≤ 100000000000000000000000 * (U + 1)^8 * B := by
    calc
      1 = 1 * 1 * 1 := by decide
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (by decide) hA) hB
  have hsucc : C + 1 ≤ 2 * (100000000000000000000000 * (U + 1)^8 * B) := by omega
  have hcoeff : 1000 * 2 * 100000000000000000000000 =
      200000000000000000000000000 := by norm_num
  have hpow : (U + 1)^10 = (U + 1) * (U + 1) * (U + 1)^8 := by
    rw [show 10 = 2 + 8 by decide, pow_add, pow_two]
  have hmul (x y : ℕ) :
      1000 * x * x * (2 * (100000000000000000000000 * x^8 * y)) =
        (1000 * 2 * 100000000000000000000000) * (x * x * x^8) * y := by
    ac_rfl
  calc
    sourceBudget (Δ := Δ) p hr hQ coefficients alphabet ≤
        1000 * (r + 1) * (Q + 1) * (C + 1) := loop_envelope r Q C
    _ ≤ 1000 * (U + 1) * (U + 1) *
        (2 * (100000000000000000000000 * (U + 1)^8 * B)) := by gcongr
    _ = (1000 * 2 * 100000000000000000000000) *
        ((U + 1) * (U + 1) * (U + 1)^8) * B := hmul (U + 1) B
    _ = 200000000000000000000000000 * (U + 1)^10 * B := by rw [hcoeff, hpow]
    _ ≤ 1000000000000000000000000000 * (U + 1)^10 * B := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))

/-- Uniform cap for the complete fixed native program. The exponent's
coefficient and degree are fixed independently of all input parameters. -/
def executionBound (U : ℕ) : ℕ := 2 ^ (2000000000000000000000000000 * (U + 1)^10)

/-- The result stack starts empty and a primitive instruction pushes at
most one bit. Thus the actual execution also bounds emitted record bytes. -/
theorem output_length_le_of_runsIn (ctx : Context) (width result : Word)
    (regs finalRegs : Fin 32 → Bool) (T : ℕ)
    (h : RunsIn program T ((inputState ctx regs).withPC (some program.entry))
      ((outputState ctx width result finalRegs).withPC none)) : result.length ≤ T := by
  obtain ⟨steps, hsteps, htrace⟩ := h
  have hb := SequentialProgram.trace_stack_length_le htrace (127 : Fin 128)
  change ((outputState ctx width result finalRegs).stacks 127).length ≤
    ((inputState ctx regs).stacks 127).length + steps at hb
  have hi : (inputState ctx regs).stacks 127 = [] := by simp [inputState]
  have ho : (outputState ctx width result finalRegs).stacks 127 = result := by simp [outputState]
  rw [hi, ho, List.length_nil, zero_add] at hb
  exact hb.trans hsteps

theorem sourceBudget_le_two_pow (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (coefficients alphabet : List (ZMod p)) (hcard : alphabet.length = p) (U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hR : coefficients.length ≤ U) (hp : p ≤ U) (hw : MatrixWordEncoding.width p ≤ U)
    (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    sourceBudget (Δ := Δ) p hr hQ coefficients alphabet ≤ executionBound U := by
  have he : 1000000 * (U + 1)^10 ≤ 1000000000000000000000000000 * (U + 1)^10 :=
    Nat.mul_le_mul_right _ (by decide)
  calc
    sourceBudget (Δ := Δ) p hr hQ coefficients alphabet ≤
        1000000000000000000000000000 * (U + 1)^10 * 2 ^ (1000000 * (U + 1)^10) :=
      sourceBudget_le_polynomial_times_search p hr hQ coefficients alphabet hcard U
        hrU hQU hΔU hR hp hw hu
    _ ≤ 2 ^ (1000000000000000000000000000 * (U + 1)^10) *
        2 ^ (1000000000000000000000000000 * (U + 1)^10) :=
      Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.pow_le_pow_right (by decide) he)
    _ = executionBound U := by
      rw [← pow_add]
      have heq : 1000000000000000000000000000 * (U + 1)^10 +
          1000000000000000000000000000 * (U + 1)^10 =
          2000000000000000000000000000 * (U + 1)^10 := by ring
      exact congrArg (fun e : ℕ => 2^e) heq

/-- The numeric bound is attached to the actual native execution and its
emitted successful basis records, with no matrix or per-color trace input. -/
theorem program_runsIn_bounded (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (hr : 0 < r) (hQ : 0 < Q) (coefficients alphabet : List (ZMod p))
    (hfull : ∀ x, x ∈ alphabet) (hcard : alphabet.length = p) (regs : Fin 32 → Bool) (U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hR : coefficients.length ≤ U) (hp : p ≤ U) (hw : MatrixWordEncoding.width p ≤ U)
    (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    ∃ rows finalRegs,
      RowsGood (GoodResult (Δ := Δ) p hr hQ coefficients) r Q rows ∧
      RunsIn program (executionBound U)
        ((inputState (canonicalContext p r Q Δ coefficients alphabet) regs).withPC
          (some program.entry))
        ((outputState (canonicalContext p r Q Δ coefficients alphabet)
          (TypeIndexProgram.unary (Q * r))
          (ProgramEncoding.encodeRecords (rows.map ProgramEncoding.encodeRecords)) finalRegs).withPC none) := by
  obtain ⟨rows, finalRegs, hg, he⟩ :=
    LocalBasisBatchProgram.program_runsIn (Δ := Δ) p h2 hr hQ coefficients alphabet hfull regs
  exact ⟨rows, finalRegs, hg, he.mono
    (sourceBudget_le_two_pow p hr hQ coefficients alphabet hcard U hrU hQU hΔU hR hp hw hu)⟩

theorem primitive_runsIn_bounded (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (hr : 0 < r) (hQ : 0 < Q) (coefficients alphabet : List (ZMod p))
    (hfull : ∀ x, x ∈ alphabet) (hcard : alphabet.length = p) (regs : Fin 32 → Bool) (U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hR : coefficients.length ≤ U) (hp : p ≤ U) (hw : MatrixWordEncoding.width p ≤ U)
    (hu : (TypeEnumeration.universalBytes r Q Δ).length ≤ U) :
    ∃ rows finalRegs,
      RowsGood (GoodResult (Δ := Δ) p hr hQ coefficients) r Q rows ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * executionBound U)
        (primitiveCfg program ((inputState (canonicalContext p r Q Δ coefficients alphabet) regs).withPC
          (some program.entry)))
        (primitiveCfg program ((outputState (canonicalContext p r Q Δ coefficients alphabet)
          (TypeIndexProgram.unary (Q * r))
          (ProgramEncoding.encodeRecords (rows.map ProgramEncoding.encodeRecords)) finalRegs).withPC none)) := by
  obtain ⟨rows, finalRegs, hg, he⟩ :=
    program_runsIn_bounded p h2 hr hQ coefficients alphabet hfull hcard regs U
      hrU hQU hΔU hR hp hw hu
  exact ⟨rows, finalRegs, hg, primitive_execution program he⟩

end SubexponentialSAT.Subexp.LocalBasisBatchBounds

end OAI.Algorithms
