import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.IntegralTranslation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralCoordinateVacuum
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TranslationFunctionalUniqueness
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FiniteIntegral
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TracePairing

/-! # Integral Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.IntegralComparison.CM

noncomputable section

/-! The restricted product of normalized local Haar integrals equals
the actual rational finite-adele Haar integral in integral-basis coordinates. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates.CM

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def transported : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Finite.AdelicTestCoordinates.CM.Index F N) →ₗ[ℂ] ℂ :=
  (LocalIntegral.CM.globalIntegral F N).comp (Finite.AdelicTestCoordinates.CM.equivalence F N).toLinearMap

theorem coset_translation (q : ℚ) (hq : q ≠ 0) (a : Finite.AdelicTestCoordinates.CM.Index F N → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    Finite.AdelicTestCoordinates.CM.equivalence F N (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a) =
      IntegralTranslation.CM.translation F N ((Finite.TracePairing.CM.position F N).symm a)
        (Finite.AdelicTestCoordinates.CM.equivalence F N (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq)) := by
  apply Subtype.ext
  funext x
  change RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq (Finite.TracePairing.CM.position F N x - a) =
    RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.latticeIndicator q hq (Finite.TracePairing.CM.position F N
      (x - (Finite.TracePairing.CM.position F N).symm a))
  rw [map_sub, ContinuousLinearEquiv.apply_symm_apply]

theorem coset (q : ℚ) (hq : q ≠ 0) (a : Finite.AdelicTestCoordinates.CM.Index F N → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    transported F N (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a) = transported F N (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeTestFunction q hq) := by
  change LocalIntegral.CM.globalIntegral F N (Finite.AdelicTestCoordinates.CM.equivalence F N (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq a)) = _
  rw [coset_translation, IntegralTranslation.CM.invariant]
  rfl

theorem vacuum : transported F N RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = 1 := by
  change LocalIntegral.CM.globalIntegral F N (Finite.AdelicTestCoordinates.CM.equivalence F N RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction) = 1
  rw [IntegralCoordinateVacuum.CM.equivalence_vacuum]
  unfold LocalIntegral.CM.globalIntegral
  rw [Finite.FunctionAction.CM.FunctionalDescent.function_pure]
  simp only [LocalIntegral.CM.vacuum, finprod_one]

theorem equality : transported F N = Rational.FiniteIntegral.CM.integral (Finite.AdelicTestCoordinates.CM.Index F N) :=
  TranslationFunctionalUniqueness.CM.unique _ _ (coset F N)
    (Rational.FiniteIntegral.CM.coset (Finite.AdelicTestCoordinates.CM.Index F N))
    ((vacuum F N).trans (Rational.FiniteIntegral.CM.vacuum (Finite.AdelicTestCoordinates.CM.Index F N)).symm)
    (by rw [Rational.FiniteIntegral.CM.vacuum]; exact one_ne_zero)
    (fun n hn => Rational.FiniteIntegral.CM.lattice_ne_zero (Finite.AdelicTestCoordinates.CM.Index F N) (n : ℚ)
      (by exact_mod_cast hn.ne'))

theorem integral (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Finite.AdelicTestCoordinates.CM.Index F N)) :
    LocalIntegral.CM.globalIntegral F N (Finite.AdelicTestCoordinates.CM.equivalence F N φ) =
      Rational.FiniteIntegral.CM.integral (Finite.AdelicTestCoordinates.CM.Index F N) φ :=
  LinearMap.congr_fun (equality F N) φ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.IntegralComparison.CM
