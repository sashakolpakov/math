import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Finite Measure -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM

noncomputable section

/-! The finite adelic Haar measure normalized by the actual integral
lattice. This construction does not take Weil data as an input. -/

open scoped Classical
open _root_.MeasureTheory OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction

variable (I : Type*) [Fintype I]

def integralCompact : TopologicalSpace.PositiveCompacts (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
  ⟨⟨(RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)), RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors_isCompact⟩, by
    rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors_isOpen.interior_eq]
    exact ⟨0, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.zero_mem⟩⟩

def measure : Measure (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) := Measure.addHaarMeasure (integralCompact I)

instance measure_haar : (measure I).IsAddHaarMeasure := inferInstanceAs
  (Measure.addHaarMeasure (integralCompact I)).IsAddHaarMeasure

theorem integral_volume :
    measure I (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) = 1 :=
  Measure.addHaarMeasure_self

theorem integral_real_volume :
    (measure I).real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors (ι := I) : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) = 1 := by
  rw [Measure.real, integral_volume, ENNReal.toReal_one]

theorem lattice_volume_pos (q : ℚ) (hq : q ≠ 0) :
    0 < (measure I).real (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) q hq : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) := by
  exact ENNReal.toReal_pos
    ((RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isOpen q hq).measure_pos (measure I) ⟨0, (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice q hq).zero_mem⟩).ne'
    (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_isCompact q hq).measure_lt_top.ne

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM
