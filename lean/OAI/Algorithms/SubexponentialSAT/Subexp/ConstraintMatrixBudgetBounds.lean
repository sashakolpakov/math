import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixSizes
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeFiberBudgetBounds

namespace OAI.Algorithms

/-! A uniform polynomial source bound for the actual one-Side matrix
construction. The entry allowance is discharged by the concrete entry
program; every filter, row, slot and final output transfer is charged. -/

namespace SubexponentialSAT.Subexp.ConstraintMatrixBudgetBounds

open BitProgram MulticolorTypes MatrixWordEncoding ConstraintMatrixProgram

variable {r Q Δ : ℕ}

def entryCap (U : ℕ) : ℕ := 500000 * (U + 1)^4

theorem slotCost_mono_entry (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) {E F : ℕ} (hEF : E ≤ F) :
    slotCost p hr hQ t g E i ≤ slotCost p hr hQ t g F i := by
  unfold slotCost ConstraintMatrixSlot.budget ConstraintMatrixRow.budget
  gcongr

private theorem budgetSum_mono (a b : ℕ → ℕ) (hab : ∀ j, a j ≤ b j)
    (fuel start : ℕ) :
    CounterForPrograms.budgetSum a start fuel ≤ CounterForPrograms.budgetSum b start fuel := by
  induction fuel generalizing start with
  | zero => simp only [CounterForPrograms.budgetSum, le_refl]
  | succ fuel ih =>
      simpa only [CounterForPrograms.budgetSum] using
        Nat.add_le_add (hab start) (ih (start + 1))

theorem budget_mono_entry (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) {E F : ℕ} (hEF : E ≤ F) :
    budget (Δ := Δ) p hr hQ t g coefficients E ≤
      budget (Δ := Δ) p hr hQ t g coefficients F := by
  have hpoint (j : ℕ) : loopCost (Δ := Δ) p hr hQ t g E j ≤
      loopCost (Δ := Δ) p hr hQ t g F j := by
    by_cases hj : j < Δ
    · simp only [loopCost, dite_eq_left hj]
      exact slotCost_mono_entry p hr hQ t g _ hEF
    · simp only [loopCost, dite_eq_right hj, le_refl]
  have h := budgetSum_mono _ _ hpoint Δ 0
  unfold budget
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right h _) _) _

theorem encodedSide_le (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)
    (U : ℕ) (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hN : (columns (Δ := Δ) hr hQ t g).length ≤ U) :
    (ProgramEncoding.encodeRecords (TypeEnumeration.sideBytes r Q Δ t.val g.val)).length ≤
      5 * (U + 1)^4 := by
  let s := U + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs4 : s ≤ s^4 := by simpa using Nat.pow_le_pow_right hs (show 1 ≤ 4 by decide)
  have ht := MatrixEntryBudgetBounds.typeWidth_le hrU hQU hΔU
  change CollisionProgram.typeWidth r Q Δ ≤ s^3 at ht
  rw [ConstraintMatrixProgram.encodedSide_length]
  change _ ≤ 5 * s^4
  calc
    _ ≤ s * (2 * s^3 + 2) + 1 := by
      exact Nat.add_le_add_right
        (Nat.mul_le_mul (hN.trans (by dsimp [s]; omega))
          (Nat.add_le_add_right (Nat.mul_le_mul_left 2 ht) 2)) 1
    _ ≤ _ := by nlinarith only [hs, hs4]

theorem row_budget_le (p E N U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hN : N ≤ U) (hw : width p ≤ U) (hE : E ≤ entryCap U) :
    ConstraintMatrixRow.budget p E N r Q Δ ≤ 501000 * (U + 1)^5 := by
  let s := U + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s^2 := by nlinarith
  have hs4 : s^2 ≤ s^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hs5 : s^4 ≤ s^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have ht := MatrixEntryBudgetBounds.typeWidth_le hrU hQU hΔU
  change CollisionProgram.typeWidth r Q Δ ≤ s^3 at ht
  change E ≤ 500000 * s^4 at hE
  change _ ≤ 501000 * s^5
  calc
    _ ≤ s * (500000 * s^4 + 11 * s^3 + 10 * s + 24) + 4 := by
      unfold ConstraintMatrixRow.budget
      gcongr <;> dsimp [s] at * <;> omega
    _ ≤ _ := by nlinarith only [hs, hs2, hs4, hs5]

theorem slot_budget_le (p N C R U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hN : N ≤ U) (hR : R ≤ U) (hw : width p ≤ U)
    (hC : C ≤ 5 * (U + 1)^4) :
    ConstraintMatrixSlot.budget p (entryCap U) N C R r Q Δ ≤
      502000 * (U + 1)^6 := by
  let s := U + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs4 : s ≤ s^4 := by simpa using Nat.pow_le_pow_right hs (show 1 ≤ 4 by decide)
  have hs5 : s^4 ≤ s^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hs6 : s^5 ≤ s^6 := Nat.pow_le_pow_right (by omega) (by omega)
  have ht := MatrixEntryBudgetBounds.typeWidth_le hrU hQU hΔU
  change CollisionProgram.typeWidth r Q Δ ≤ s^3 at ht
  have hrow := row_budget_le p (entryCap U) N U hrU hQU hΔU hN hw le_rfl
  change ConstraintMatrixRow.budget p (entryCap U) N r Q Δ ≤ 501000 * s^5 at hrow
  change C ≤ 5 * s^4 at hC
  change _ ≤ 502000 * s^6
  calc
    _ ≤ s * (501000 * s^5 + 11 * s^3 + 7 * (5 * s^4) + 20) + 4 := by
      unfold ConstraintMatrixSlot.budget
      gcongr
      all_goals dsimp [s] at *
      all_goals omega
    _ ≤ _ := by nlinarith only [hs, hs4, hs5, hs6]

theorem slotCost_le (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U) (hw : width p ≤ U)
    (hN : (columns (Δ := Δ) hr hQ t g).length ≤ U) :
    slotCost p hr hQ t g (entryCap U) i ≤ 504000 * (U + 1)^6 := by
  have hside : (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length ≤ U := by
    simpa only [columns, List.length_map] using hN
  have hf := TypeFiberBudgetBounds.joint_budget_le hr hQ i t g U hrU hQU hΔU hside
  have hC := encodedSide_le hr hQ t g U hrU hQU hΔU hN
  have hR := (rows_length_le_columns hr hQ t g i).trans hN
  have hslot := slot_budget_le p _ _ _ U hrU hQU hΔU hN hR hw hC
  have hs : 1 ≤ U + 1 := by omega
  have h46 : (U + 1)^4 ≤ (U + 1)^6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h06 : 1 ≤ (U + 1)^6 := by
    simpa using Nat.pow_le_pow_right hs (show 0 ≤ 6 by decide)
  unfold slotCost
  nlinarith only [hf, hslot, h06, h46]

theorem matrixBytes_length_le (p : ℕ) [Fact p.Prime]
    (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)
    (coefficients : List (ZMod p)) (U : ℕ) (hΔU : Δ ≤ U) (hw : width p ≤ U)
    (hN : (columns (Δ := Δ) hr hQ t g).length ≤ U) :
    (matrixBytes (Δ := Δ) p hr hQ t g coefficients).length ≤ 3 * (U + 1)^4 := by
  let s := U + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs34 : s^3 ≤ s^4 := Nat.pow_le_pow_right (by omega) (by omega)
  apply (ConstraintMatrixProgram.matrixBytes_length_le p hr hQ t g coefficients).trans
  change _ ≤ 3 * s^4
  calc
    _ ≤ s * s^2 * (2 * s + 1) := by gcongr <;> dsimp [s] at * <;> omega
    _ ≤ _ := by nlinarith only [hs34]

theorem budget_le (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) (U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U) (hw : width p ≤ U)
    (hN : (columns (Δ := Δ) hr hQ t g).length ≤ U) :
    budget (Δ := Δ) p hr hQ t g coefficients (entryCap U) ≤ 10000000 * (U + 1)^8 := by
  let s := U + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hs18 : s ≤ s^8 := by simpa using Nat.pow_le_pow_right hs (show 1 ≤ 8 by decide)
  have hs48 : s^4 ≤ s^8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hs78 : s^7 ≤ s^8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hloop := CounterForPrograms.budgetSum_le
    (loopCost (Δ := Δ) p hr hQ t g (entryCap U)) 0 Δ (504000 * s^6) (by
      intro j _ hj
      have hj' : j < Δ := by omega
      simpa only [loopCost, dite_eq_left hj'] using
        slotCost_le p hr hQ t g ⟨j, hj'⟩ U hrU hQU hΔU hw hN)
  have hmatrix := matrixBytes_length_le p hr hQ t g coefficients U hΔU hw hN
  change _ ≤ 3 * s^4 at hmatrix
  change _ ≤ 10000000 * s^8
  calc
    _ ≤ Δ * (504000 * s^6) + 2 * Δ + 9 * s^4 + 8 := by
      unfold budget
      omega
    _ ≤ s * (504000 * s^6) + 2 * s + 9 * s^4 + 8 := by
      gcongr <;> dsimp [s] <;> omega
    _ ≤ _ := by nlinarith only [hs, hs18, hs48, hs78]

theorem budget_le_of_entryCap (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) (E U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U) (hw : width p ≤ U)
    (hN : (columns (Δ := Δ) hr hQ t g).length ≤ U) (hE : E ≤ entryCap U) :
    budget (Δ := Δ) p hr hQ t g coefficients E ≤ 10000000 * (U + 1)^8 :=
  (budget_mono_entry p hr hQ t g coefficients hE).trans
    (budget_le p hr hQ t g coefficients U hrU hQU hΔU hw hN)

/-- Actual source execution with the concrete entry cost fully discharged. -/
theorem program_runsIn (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)
    (coefficients : List (ZMod p)) (regs : Fin 18 → Bool) (U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hR : coefficients.length ≤ U) (hw : width p ≤ U)
    (hN : (columns (Δ := Δ) hr hQ t g).length ≤ U) :
    ∃ out, RunsIn ConstraintMatrixProgram.program (10000000 * (U + 1)^8)
      ((ConstraintMatrixProgram.input p r Q Δ t.val g.val coefficients
        (TypeEnumeration.sideBytes r Q Δ t.val g.val) regs).withPC
        (some ConstraintMatrixProgram.program.entry))
      ((ConstraintMatrixProgram.output (Δ := Δ) p hr hQ t g coefficients out).withPC none) := by
  have hE : ∀ i : Fin Δ, ∀ u ∈ rows hr hQ t g i, ∀ y ∈ columns hr hQ t g,
      ConstraintEntryProgram.programBudget p i t u y coefficients ≤ entryCap U := by
    intro i u _ y _
    exact MatrixEntryBudgetBounds.constraint_programBudget_le p i t u y coefficients U
      hrU hQU hΔU hR hw
  obtain ⟨out, n, hn, ht⟩ := ConstraintMatrixProgram.program_runsIn p h2 hr hQ t g coefficients
    (entryCap U) hE regs
  exact ⟨out, n, hn.trans (budget_le p hr hQ t g coefficients U hrU hQU hΔU hw hN), ht⟩

theorem primitive_runsIn (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)
    (coefficients : List (ZMod p)) (regs : Fin 18 → Bool) (U : ℕ)
    (hrU : r ≤ U) (hQU : Q ≤ U) (hΔU : Δ ≤ U)
    (hR : coefficients.length ≤ U) (hw : width p ≤ U)
    (hN : (columns (Δ := Δ) hr hQ t g).length ≤ U) :
    ∃ out, Computation.RunsIn (BitProgram.primitive ConstraintMatrixProgram.program).step
      (BitProgram.primitiveOverhead ConstraintMatrixProgram.program * (10000000 * (U + 1)^8))
      (BitProgram.primitiveCfg ConstraintMatrixProgram.program
        ((ConstraintMatrixProgram.input p r Q Δ t.val g.val coefficients
          (TypeEnumeration.sideBytes r Q Δ t.val g.val) regs).withPC
          (some ConstraintMatrixProgram.program.entry)))
      (BitProgram.primitiveCfg ConstraintMatrixProgram.program
        ((ConstraintMatrixProgram.output (Δ := Δ) p hr hQ t g coefficients out).withPC none)) := by
  obtain ⟨out, ht⟩ := program_runsIn p h2 hr hQ t g coefficients regs U hrU hQU hΔU hR hw hN
  exact ⟨out, BitProgram.primitive_execution _ ht⟩

end SubexponentialSAT.Subexp.ConstraintMatrixBudgetBounds

end OAI.Algorithms
