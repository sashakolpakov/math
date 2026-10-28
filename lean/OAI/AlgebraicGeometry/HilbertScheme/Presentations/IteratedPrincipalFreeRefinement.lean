import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.LocalizationFreeRefinement
import Mathlib.RingTheory.Nilpotent.Basic

/-! # Iterated Principal Free Refinement -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedPrincipalFreeRefinement

noncomputable section

/-! A principal open inside a principal domain chart contains a principal
open from the original ring. The refinement retains freeness. -/

open TensorProduct

universe u
variable {R : Type u} [CommRing R]

theorem principal_domain_element_refinement (a : R) [IsDomain (Localization.Away a)]
    (t : Localization.Away a) (ht : t ≠ 0) :
    ∃ r : R, ¬ IsNilpotent (a * r) ∧
      ∃ φ : Localization.Away a →+* Localization.Away (a * r),
        (∀ x : R, φ (algebraMap R (Localization.Away a) x) =
          algebraMap R (Localization.Away (a * r)) x) ∧ IsUnit (φ t) := by
  let A := Localization.Away a
  obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj a t
  have ha : IsUnit (algebraMap R A a) := IsLocalization.Away.algebraMap_isUnit a
  have hr0 : algebraMap R A r ≠ 0 := by
    rw [← hr]
    exact mul_ne_zero ht (pow_ne_zero _ ha.ne_zero)
  have har : ¬ IsNilpotent (a * r) := by
    intro hnil
    have hz : algebraMap R A (a * r) = 0 :=
      (hnil.map (algebraMap R A)).eq_zero
    rw [map_mul] at hz
    exact mul_ne_zero ha.ne_zero hr0 hz
  let C := Localization.Away (a * r)
  have hau : IsUnit (algebraMap R C a) :=
    IsLocalization.Away.isUnit_of_dvd (a * r) (dvd_mul_right a r)
  have hru : IsUnit (algebraMap R C r) :=
    IsLocalization.Away.isUnit_of_dvd (a * r) (dvd_mul_left r a)
  let φ : A →+* C := IsLocalization.Away.lift a hau
  have hφ (x : R) : φ (algebraMap R A x) = algebraMap R C x :=
    IsLocalization.Away.lift_eq a hau x
  have he : φ t * algebraMap R C a ^ n = algebraMap R C r := by
    have h := congrArg φ hr
    change φ (t * algebraMap R A a ^ n) = φ (algebraMap R A r) at h
    simpa only [map_mul, map_pow, hφ] using h
  refine ⟨r, har, φ, hφ, ?_⟩
  exact isUnit_of_mul_isUnit_left (he.symm ▸ hru)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedPrincipalFreeRefinement
