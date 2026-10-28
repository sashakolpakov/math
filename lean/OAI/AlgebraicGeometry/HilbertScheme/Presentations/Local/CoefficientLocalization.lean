import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.Submodule

/-! # Coefficient Localization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.CoefficientLocalization

noncomputable section

/-! Localize a coefficient ring at the inverse image of the closed point
of a local target. The resulting ring still maps to the target. -/

universe u v w
variable {C : Type u} [CommRing C] {A : Type v} [CommRing A] [IsLocalRing A]

def localCoefficientPrime (f : C →+* A) : Ideal C :=
  (IsLocalRing.maximalIdeal A).comap f

instance localCoefficientPrime_isPrime (f : C →+* A) : (localCoefficientPrime f).IsPrime :=
  Ideal.comap_isPrime f (IsLocalRing.maximalIdeal A)

theorem localCoefficientPrime_map_unit (f : C →+* A) (s : (localCoefficientPrime f).primeCompl) :
    IsUnit (f s.val) := by
  have h : f s.val ∉ IsLocalRing.maximalIdeal A := s.property
  simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using h

def localCoefficientLocalizationMap (f : C →+* A) :
    Localization.AtPrime (localCoefficientPrime f) →+* A :=
  IsLocalization.lift (S := Localization.AtPrime (localCoefficientPrime f))
    (localCoefficientPrime_map_unit f)

theorem localCoefficientLocalizationMap_comp (f : C →+* A) :
    (localCoefficientLocalizationMap f).comp
      (algebraMap C (Localization.AtPrime (localCoefficientPrime f))) = f :=
  IsLocalization.lift_comp _

theorem localCoefficientLocalizationMap_isLocalHom (f : C →+* A) :
    IsLocalHom (localCoefficientLocalizationMap f) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (localCoefficientPrime f).primeCompl x
  apply (IsLocalization.AtPrime.isUnit_mk'_iff _ _ r s).mpr
  have hf : IsUnit (f r) := by
    have he := IsLocalization.mk'_spec (Localization.AtPrime (localCoefficientPrime f)) r s
    have he' := congrArg (localCoefficientLocalizationMap f) he
    simp only [map_mul, localCoefficientLocalizationMap, IsLocalization.lift_eq] at he'
    rw [← he']
    exact hx.mul (localCoefficientPrime_map_unit f s)
  intro hr
  exact ((IsLocalRing.mem_maximalIdeal (f r)).mp hr) hf

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.CoefficientLocalization
