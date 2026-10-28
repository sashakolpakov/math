import OAI.AlgebraicGeometry.Divisors.LineBundles.PositiveOrderIs
import Mathlib.Analysis.AbsoluteValue.Equivalence

/-! # DVR Absolute Value -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DVRAbsoluteValue.BundleCycles

noncomputable section

/-! The real absolute value of an actual DVR and its fraction field.
It retains the same valuation ring and distinguishes the same orders. -/

open scoped NNReal

variable (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]

def dvrAbsoluteValue : AbsoluteValue K ℝ :=
  (IsDiscreteValuationRing.maximalIdeal A).adicAbv (by norm_num : (1 : ℝ≥0) < 2)

theorem dvrAbsoluteValue_le_iff (x y : K) :
    dvrAbsoluteValue A K x ≤ dvrAbsoluteValue A K y ↔
      (IsDiscreteValuationRing.maximalIdeal A).valuation K x ≤
        (IsDiscreteValuationRing.maximalIdeal A).valuation K y := by
  change ((WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) _ : ℝ≥0) : ℝ) ≤
    ((WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) _ : ℝ≥0) : ℝ) ↔ _
  exact NNReal.coe_le_coe.trans
    (WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2)).le_iff_le

theorem dvrAbsoluteValue_lt_iff (x y : K) :
    dvrAbsoluteValue A K x < dvrAbsoluteValue A K y ↔
      (IsDiscreteValuationRing.maximalIdeal A).valuation K x <
        (IsDiscreteValuationRing.maximalIdeal A).valuation K y := by
  rw [lt_iff_not_ge, lt_iff_not_ge, dvrAbsoluteValue_le_iff]

theorem dvrAbsoluteValue_eq_iff (x y : K) :
    dvrAbsoluteValue A K x = dvrAbsoluteValue A K y ↔
      (IsDiscreteValuationRing.maximalIdeal A).valuation K x =
        (IsDiscreteValuationRing.maximalIdeal A).valuation K y := by
  rw [le_antisymm_iff, le_antisymm_iff, dvrAbsoluteValue_le_iff, dvrAbsoluteValue_le_iff]

theorem dvrAbsoluteValue_nontrivial : (dvrAbsoluteValue A K).IsNontrivial := by
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal A).valuation_exists_uniformizer K
  refine ⟨π, ?_, ?_⟩
  · intro h
    rw [h, map_zero] at hπ
    exact WithZero.coe_ne_zero hπ.symm
  · intro h
    have he := (dvrAbsoluteValue_eq_iff A K π 1).mp (h.trans (map_one _).symm)
    rw [hπ, map_one] at he
    exact (by decide : WithZero.exp (-1 : ℤ) ≠ 1) he

theorem dvrAbsoluteValue_le_one_iff (x : K) :
    dvrAbsoluteValue A K x ≤ 1 ↔ ∃ a : A, algebraMap A K a = x := by
  have he : dvrAbsoluteValue A K x ≤ 1 ↔
      (IsDiscreteValuationRing.maximalIdeal A).valuation K x ≤ 1 := by
    simpa only [map_one] using dvrAbsoluteValue_le_iff A K x 1
  rw [he]
  exact ⟨IsDiscreteValuationRing.exists_lift_of_le_one, fun ⟨a, ha⟩ =>
    ha ▸ (IsDiscreteValuationRing.maximalIdeal A).valuation_le_one a⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DVRAbsoluteValue.BundleCycles
