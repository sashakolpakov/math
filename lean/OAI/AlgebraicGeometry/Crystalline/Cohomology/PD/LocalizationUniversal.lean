import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Localization

/-! # Localization Universal -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.LocalizationUniversal.PDLocalizationUniversal

noncomputable section

/-!
# Universal compatibility of localized divided powers

A ring map out of a localization preserves the localized divided powers
whenever its composite with the original coefficient map preserves divided
powers. In particular the localized divided-power structure is uniquely
determined by compatibility with the original ring.
-/

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S] (I : Ideal R) (δ : DividedPowers I)

local notation "J" => I.map (algebraMap R S)
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Localization.PDLocalization.dividedPowers R S M I δ

theorem map_isDPMorphism (T : Type u) [CommRing T] (L : Ideal T) (ε : DividedPowers L)
    (f : S →+* T) (hf : DividedPowers.IsDPMorphism δ ε (f.comp (algebraMap R S))) :
    DividedPowers.IsDPMorphism γ ε f where
  ideal_comp := by
    rw [Ideal.map_map]
    exact hf.ideal_comp
  dpow_comp {n} z hz := by
    change ε.dpow n (f z) = f (LocalizationOperations.PDLocalizationOperations.dpow R S M I δ n z)
    rw [LocalizationOperations.PDLocalizationOperations.representative_spec R S M I z hz]
    let v := LocalizationOperations.PDLocalizationOperations.representative R S M I z hz
    change ε.dpow n (f (IsLocalization.mk' S (v.1 : R) v.2)) =
      f (LocalizationOperations.PDLocalizationOperations.dpow R S M I δ n (IsLocalization.mk' S (v.1 : R) v.2))
    rw [Localization.PDLocalization.fraction_formula R S M I δ n _ v.1.property, map_mul, map_pow,
      IsLocalization.mk'_eq_mul_mk'_one (S := S) (v.1 : R) v.2, map_mul]
    have hv : f (algebraMap R S (v.1 : R)) ∈ L :=
      hf.ideal_comp (Ideal.mem_map_of_mem (f.comp (algebraMap R S)) v.1.property)
    rw [mul_comm (f (algebraMap R S (v.1 : R))) (f (IsLocalization.mk' S 1 v.2)), ε.dpow_mul hv]
    have hd : ε.dpow n (f (algebraMap R S (v.1 : R))) = f (algebraMap R S (δ.dpow n v.1)) :=
      hf.dpow_comp v.1 v.1.property
    rw [hd, mul_comm]

theorem unique (ε : DividedPowers J)
    (hε : DividedPowers.IsDPMorphism δ ε (algebraMap R S)) : γ = ε := by
  have he := map_isDPMorphism R S M I δ S J ε (RingHom.id S) hε
  apply DividedPowers.ext
  intro n z hz
  exact (he.dpow_comp z hz).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.LocalizationUniversal.PDLocalizationUniversal
