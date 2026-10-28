import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Valuation Birational Local -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ValuationBirationalLocal.BundleCycles.ValuationBirational

noncomputable section

/-! A local birational extension of a valuation ring is an isomorphism.
This gives the local-ring comparison for proper birational maps over a
codimension-one point of a normal scheme. -/

theorem algebraMap_bijective (R A K : Type*) [CommRing R] [CommRing A]
    [IsDomain R] [ValuationRing R] [IsDomain A] [Field K]
    [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
    [IsFractionRing R K] [IsFractionRing A K] [IsLocalHom (algebraMap R A)] :
    Function.Bijective (algebraMap R A) := by
  have hiA := IsFractionRing.injective A K
  have hiR : Function.Injective (algebraMap R A) := by
    apply Function.Injective.of_comp (f := algebraMap A K)
    simpa only [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq] using IsFractionRing.injective R K
  refine ⟨hiR, fun a => ?_⟩
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha]⟩
  have haK : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ hiA).mpr ha
  obtain ⟨r, hr⟩ | ⟨r, hr⟩ :=
    (ValuationRing.iff_isInteger_or_isInteger R K).mp inferInstance (algebraMap A K a)
  · refine ⟨r, hiA ?_⟩
    rw [← IsScalarTower.algebraMap_apply]
    exact hr
  · have he : algebraMap R A r * a = 1 := by
      apply hiA
      rw [map_mul, ← IsScalarTower.algebraMap_apply, hr, inv_mul_cancel₀ haK, map_one]
    have hu : IsUnit r := isUnit_of_map_unit (algebraMap R A) r (IsUnit.of_mul_eq_one a he)
    obtain ⟨v, hv⟩ := hu
    refine ⟨↑v⁻¹, hiA ?_⟩
    rw [← IsScalarTower.algebraMap_apply, map_units_inv, hv, hr, inv_inv]

def birationalLocalEquiv (R A K : Type*) [CommRing R] [CommRing A]
    [IsDomain R] [ValuationRing R] [IsDomain A] [Field K]
    [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
    [IsFractionRing R K] [IsFractionRing A K] [IsLocalHom (algebraMap R A)] : R ≃ₐ[R] A :=
  AlgEquiv.ofBijective (Algebra.ofId R A) (algebraMap_bijective R A K)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ValuationBirationalLocal.BundleCycles.ValuationBirational
