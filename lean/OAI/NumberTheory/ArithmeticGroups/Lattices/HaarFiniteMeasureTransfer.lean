import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Haar Finite Measure Transfer -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.HaarFiniteMeasureTransfer.Construction

noncomputable section

/-! Finiteness for one right Haar measure implies finiteness for every
right Haar measure on a locally compact second countable group. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure
open scoped ENNReal

theorem inverseHaar_finite_of_rightHaar_finite
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ ν : Measure G) [IsHaarMeasure μ] [IsHaarMeasure ν.inv]
    (S : Set G) (hS : ν S < ⊤) : μ.inv S < ⊤ := by
  have hm := isMulLeftInvariant_eq_smul μ ν.inv
  have hi : μ.inv = haarScalarFactor μ ν.inv • ν := by
    conv_lhs => rw [hm]
    rw [Measure.inv_def, Measure.map_smul _ measurable_inv.aemeasurable, ← Measure.inv_def, Measure.inv_inv]
  rw [hi, Measure.smul_apply]
  change (haarScalarFactor μ ν.inv : ℝ≥0∞) * ν S < ⊤
  exact ENNReal.mul_lt_top (by simp) hS

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.HaarFiniteMeasureTransfer.Construction
