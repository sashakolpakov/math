import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.NatVolume

/-! # Finite Integral -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FiniteIntegral.CM

noncomputable section

/-! The actual normalized rational finite-adele Haar integral, as a
linear functional with exact lattice values and translation invariance. -/

open scoped Classical
open _root_.MeasureTheory

variable (I : Type*) [Fintype I]

def integral : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I →ₗ[ℂ] ℂ where
  toFun f := ∫ x, f.val x ∂ Constructed.FiniteMeasure.CM.measure I
  map_add' f h := integral_add (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteSchwartz_integrable f _) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteSchwartz_integrable h _)
  map_smul' c f := integral_smul c f.val

theorem lattice_value (q : ℚ) (hq : q ≠ 0) :
    integral I (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq) =
      ((Constructed.FiniteMeasure.CM.measure I).real
        (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) q hq : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) : ℂ) := by
  change (∫ x, (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (ι := I) q hq : Set (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)).indicator (fun _ => (1 : ℂ)) x
    ∂ Constructed.FiniteMeasure.CM.measure I) = _
  rw [integral_indicator_const (1 : ℂ) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice_measurableSet q hq), Complex.real_smul, mul_one]

theorem lattice_ne_zero (q : ℚ) (hq : q ≠ 0) : integral I (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq) ≠ 0 := by
  rw [lattice_value]
  exact Complex.ofReal_ne_zero.mpr (Constructed.FiniteMeasure.CM.lattice_volume_pos I q hq).ne'

theorem vacuum : integral I RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = 1 := by
  have hv : (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction 1 one_ne_zero : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction :=
    Subtype.ext Finite.IntegralVacuum.CM.latticeIndicator_one
  rw [← hv, lattice_value]
  have h := Finite.NatVolume.CM.finiteLattice_nat_volume I 1 (by decide)
  simp only [Nat.cast_one, one_pow, inv_one] at h
  rw [h, Complex.ofReal_one]

theorem coset (q : ℚ) (hq : q ≠ 0) (a : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    integral I (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a) = integral I (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq) :=
  integral_sub_right_eq_self (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq) a

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FiniteIntegral.CM
