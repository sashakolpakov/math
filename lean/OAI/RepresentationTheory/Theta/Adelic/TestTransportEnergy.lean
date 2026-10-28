import OAI.RepresentationTheory.Weil.Local.FieldCoordinates

/-! # Test Transport Energy -/

namespace OAI.RepresentationTheory.Theta.Adelic.TestTransportEnergy

noncomputable section

/-! Exact positive energy scaling under changes of local field coordinates,
for the native reference Haar measures. -/

open _root_.MeasureTheory OAI.RepresentationTheory.Weil.Local.FieldCoordinates.Construction
open scoped NNReal

variable {k l : Type} [NormedField k] [NormedField l] [LocallyCompactSpace k] [LocallyCompactSpace l]
variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
variable [SecondCountableTopology k] [SecondCountableTopology l] {m n : ℕ}

def transportEnergyScale (e : Weil.Local.FunctionsMetaplectic.Construction.Position k m ≃ₜ+ Weil.Local.FunctionsMetaplectic.Construction.Position l n) : ℝ≥0 :=
  Measure.addHaarScalarFactor ((Weil.Local.UnitaryInner.Construction.referencePositionMeasure l n).map e.symm) (Weil.Local.UnitaryInner.Construction.referencePositionMeasure k m)

theorem transportEnergyScale_pos (e : Weil.Local.FunctionsMetaplectic.Construction.Position k m ≃ₜ+ Weil.Local.FunctionsMetaplectic.Construction.Position l n) :
    0 < transportEnergyScale e := by
  let : ((Weil.Local.UnitaryInner.Construction.referencePositionMeasure l n).map e.symm).IsAddHaarMeasure :=
    e.symm.isAddHaarMeasure_map (Weil.Local.UnitaryInner.Construction.referencePositionMeasure l n)
  exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
    ((Weil.Local.UnitaryInner.Construction.referencePositionMeasure l n).map e.symm) (Weil.Local.UnitaryInner.Construction.referencePositionMeasure k m)

theorem testSpaceTransport_energy (e : Weil.Local.FunctionsMetaplectic.Construction.Position k m ≃ₜ+ Weil.Local.FunctionsMetaplectic.Construction.Position l n) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k m) :
    Weil.Local.FunctionsMetaplectic.Construction.l2Energy l n (Weil.Local.FieldCoordinates.Construction.testSpaceTransport e f) = (transportEnergyScale e : ℝ) * Weil.Local.FunctionsMetaplectic.Construction.l2Energy k m f := by
  let μ := Weil.Local.UnitaryInner.Construction.referencePositionMeasure l n
  let ν := Weil.Local.UnitaryInner.Construction.referencePositionMeasure k m
  let : (μ.map e.symm).IsAddHaarMeasure := e.symm.isAddHaarMeasure_map μ
  have hμ := Measure.isAddLeftInvariant_eq_smul_of_regular (μ.map e.symm) ν
  have h := integral_map_equiv (μ := μ) e.symm.toHomeomorph.toMeasurableEquiv (fun x => ‖f.val x‖ ^ 2)
  change (∫ x, ‖f.val x‖ ^ 2 ∂μ.map e.symm) = _ at h
  rw [hμ, integral_smul_nnreal_measure] at h
  exact h.symm

theorem testSpaceTransport_sqrt_energy (e : Weil.Local.FunctionsMetaplectic.Construction.Position k m ≃ₜ+ Weil.Local.FunctionsMetaplectic.Construction.Position l n) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k m) :
    Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.l2Energy l n (Weil.Local.FieldCoordinates.Construction.testSpaceTransport e f)) =
      Real.sqrt (transportEnergyScale e : ℝ) * Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.l2Energy k m f) := by
  rw [testSpaceTransport_energy, Real.sqrt_mul (transportEnergyScale e).coe_nonneg]

end

end OAI.RepresentationTheory.Theta.Adelic.TestTransportEnergy
