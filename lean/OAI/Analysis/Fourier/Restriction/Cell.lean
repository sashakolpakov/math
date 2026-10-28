import OAI.Analysis.Fourier.WavePackets.PeriodicKernel
import OAI.Analysis.Fourier.Restriction.LatticeBound

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem measurableSet_unitCell (n : ℕ) : MeasurableSet (OAI.Analysis.Fourier.WavePackets.unitCell n) := by
  exact ZSpan.fundamentalDomain_measurableSet _

theorem volume_unitCell (n : ℕ) : volume (OAI.Analysis.Fourier.WavePackets.unitCell n) = 1 := by
  have H := OAI.Analysis.Fourier.WavePackets.lintegral_torus_eq_unitCell (n := n) (fun _ ↦ (1 : ℝ≥0∞))
  simpa only [lintegral_one, Measure.restrict_apply_univ, measure_univ] using H.symm

instance unitCell_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure ((volume : Measure (Space n)).restrict (OAI.Analysis.Fourier.WavePackets.unitCell n)) := by
  constructor
  rw [Measure.restrict_apply_univ, volume_unitCell]

end OAI.Analysis.Fourier.Restriction
