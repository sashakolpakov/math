import OAI.NumberTheory.Quaternion.Arithmetic.LocalBinaryNorm
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-! # Norm Residue Field -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.NormResidueField

noncomputable section

section

/-! The residue field of the norm valuation on a proper ultrametric
field is finite, and its zero class is detected by norm less than one. -/

open scoped Classical NNReal NormedField
open IsLocalRing

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]

abbrev normIntegerRing := (NormedField.valuation (K := K)).integer

theorem normIntegerRing_norm_le_one (x : normIntegerRing K) : ‖(x : K)‖ ≤ 1 := x.property

theorem normIntegerRing_residue_zero (x : normIntegerRing K) :
    residue (normIntegerRing K) x = 0 ↔ ‖(x : K)‖ < 1 := by
  rw [residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  exact NNReal.coe_lt_coe.symm

theorem normIntegerRing_finite_residue [ProperSpace K] : Finite (ResidueField (normIntegerRing K)) := by
  have he : (normIntegerRing K : Set K) = Metric.closedBall 0 1 := by
    ext x
    change ‖x‖₊ ≤ 1 ↔ dist x 0 ≤ 1
    rw [dist_zero_right]
    exact NNReal.coe_le_coe.symm
  have hc : IsCompact (normIntegerRing K : Set K) := by
    rw [he]
    exact isCompact_closedBall _ _
  have hcompact : CompactSpace (normIntegerRing K) := isCompact_iff_compactSpace.mp hc
  let : (Valued.v : Valuation K ℝ≥0).RankOne :=
    inferInstanceAs ((NormedField.valuation (K := K)).RankOne)
  exact (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := K) (Γ₀ := ℝ≥0)).mp hcompact |>.2.2

theorem normIntegerRing_residue_char_ne_two (h2 : ‖(2 : K)‖ = 1) :
    ringChar (ResidueField (normIntegerRing K)) ≠ 2 := by
  intro hchar
  have hz : (2 : ResidueField (normIntegerRing K)) = 0 := by
    simpa only [hchar, Nat.cast_ofNat] using CharP.cast_eq_zero (ResidueField (normIntegerRing K))
      (ringChar (ResidueField (normIntegerRing K)))
  have hres : residue (normIntegerRing K) (2 : normIntegerRing K) = 0 := by
    simpa only [map_ofNat] using hz
  have hn := (normIntegerRing_residue_zero K (2 : normIntegerRing K)).mp hres
  change ‖(2 : K)‖ < 1 at hn
  rw [h2] at hn
  exact (lt_irrefl 1) hn

end

/-! A binary quaternion norm equation with unit coefficients is
solvable over any proper ultrametric field whose residue characteristic
is odd. -/

open scoped Classical

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]

theorem unit_binary_norm_surjective (a b : K) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (h2 : ‖(2 : K)‖ = 1) : ∃ x y : K, x ^ 2 - a * y ^ 2 = b := by
  let R := normIntegerRing K
  let : Finite (IsLocalRing.ResidueField R) := normIntegerRing_finite_residue K
  let aR : R := ⟨a, ha.le⟩
  let bR : R := ⟨b, hb.le⟩
  exact LocalBinaryNorm.local_binary_norm_surjective R (normIntegerRing_norm_le_one K)
    (normIntegerRing_residue_zero K) (normIntegerRing_residue_char_ne_two K h2)
    h2 aR bR ha hb

end

end OAI.NumberTheory.Quaternion.Arithmetic.NormResidueField
