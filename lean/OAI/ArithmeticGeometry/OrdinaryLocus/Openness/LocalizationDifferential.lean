import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! # Localization Differential -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LocalizationDifferential.Construction

noncomputable section

/-! Extending a zero differential from a coordinate ring to its fraction field. -/

theorem differential_algebraMap_fractionField_eq_zero
    (k R K L : Type*) [CommRing k] [CommRing R] [Field K] [Field L]
    [Algebra k R] [Algebra R K] [IsFractionRing R K]
    [Algebra k K] [IsScalarTower k R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra k L] [IsScalarTower k R L] [IsScalarTower k K L]
    (h : ∀ r : R, KaehlerDifferential.D k L (algebraMap R L r) = 0)
    (x : K) : KaehlerDifferential.D k L (algebraMap K L x) = 0 := by
  obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj (nonZeroDivisors R) x
  have hd := congrArg (fun z : K => KaehlerDifferential.D k L (algebraMap K L z)) he
  rw [map_mul, Derivation.leibniz, ← IsScalarTower.algebraMap_apply R K L,
    ← IsScalarTower.algebraMap_apply R K L, h, h, smul_zero, zero_add] at hd
  have hu : IsUnit (algebraMap R L s) := by
    rw [IsScalarTower.algebraMap_apply R K L]
    exact (IsLocalization.map_units K s).map (algebraMap K L)
  exact hu.smul_eq_zero.mp hd

/-- The induced map of differential modules vanishes once it vanishes
on the source coordinate ring. -/
theorem map_kaehler_fractionField_eq_zero
    (k R K L : Type*) [CommRing k] [CommRing R] [Field K] [Field L]
    [Algebra k R] [Algebra R K] [IsFractionRing R K]
    [Algebra k K] [IsScalarTower k R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra k L] [IsScalarTower k R L] [IsScalarTower k K L]
    (h : ∀ r : R, KaehlerDifferential.D k L (algebraMap R L r) = 0) :
    KaehlerDifferential.map k k K L = 0 := by
  apply Derivation.liftKaehlerDifferential_unique
  ext x
  change KaehlerDifferential.map k k K L (KaehlerDifferential.D k K x) = 0
  rw [KaehlerDifferential.map_D]
  exact differential_algebraMap_fractionField_eq_zero k R K L h x

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LocalizationDifferential.Construction
