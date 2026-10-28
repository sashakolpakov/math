import OAI.AlgebraicGeometry.Divisors.LineBundles.BaseLocalizationDetection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SymmetricLocalization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeConormalNaturality

/-! # Cone Local Detection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeLocalDetection.BundleCycles

noncomputable section

/-! # LineBundleCycles: injectivity of the canonical normal-cone map is local on the coefficient ring -/

variable {R : Type} [CommRing R] (I : Ideal R)

theorem normalConeSymmetricMap_localization_congr {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (hpq : p = q)
    (h : Function.Injective (ConeSymmetric.BundleCycles.normalConeSymmetricMap (I.map (algebraMap R (Localization.AtPrime p))))) :
    Function.Injective (ConeSymmetric.BundleCycles.normalConeSymmetricMap (I.map (algebraMap R (Localization.AtPrime q)))) := by
  subst q
  exact h

theorem normalConeSymmetricMap_injective_of_localizations
    (h : ∀ (p : Ideal R) [p.IsMaximal], Function.Injective
      (ConeSymmetric.BundleCycles.normalConeSymmetricMap (I.map (algebraMap R (Localization.AtPrime p))))) :
    Function.Injective (ConeSymmetric.BundleCycles.normalConeSymmetricMap I) := by
  apply (injective_iff_map_eq_zero (ConeSymmetric.BundleCycles.normalConeSymmetricMap I)).mpr
  intro x hx
  let β : R →+* SymmetricAlgebra (R ⧸ I) I.Cotangent :=
    (algebraMap (R ⧸ I) (SymmetricAlgebra (R ⧸ I) I.Cotangent)).comp (Ideal.Quotient.mk I)
  let Aₚ (p : Ideal R) [p.IsMaximal] :=
    SymmetricAlgebra (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p)))
      (I.map (algebraMap R (Localization.AtPrime p))).Cotangent
  let ρ (p : Ideal R) [p.IsMaximal] : SymmetricAlgebra (R ⧸ I) I.Cotangent →+* Aₚ p :=
    Conormal.ConormalRestriction.BundleCycles.conormalSymmetricRestriction I (I.map (algebraMap R (Localization.AtPrime p)))
      (algebraMap R (Localization.AtPrime p)) Ideal.le_comap_map
  apply BaseLocalizationDetection.BundleCycles.ringElement_eq_zero_of_base_localizations β Aₚ ρ ?_ x ?_
  · intro p hp
    have hL := Conormal.SymmetricLocalization.BundleCycles.conormalSymmetricBase_isLocalization I (Localization.AtPrime p) p.primeCompl
    have hD : Conormal.SymmetricLocalization.BundleCycles.conormalSymmetricDenominators I p.primeCompl = p.primeCompl.map β := by
      ext y
      constructor
      · rintro ⟨a, ⟨r, hr, rfl⟩, rfl⟩
        exact ⟨r, hr, rfl⟩
      · rintro ⟨r, hr, rfl⟩
        exact ⟨Ideal.Quotient.mk I r, ⟨r, hr, rfl⟩, rfl⟩
    rw [hD] at hL
    exact hL
  · intro p hp
    apply (h p)
    rw [map_zero]
    have hn := DFunLike.congr_fun (ConeConormalNaturality.BundleCycles.normalConeSymmetricMap_naturality I
      (I.map (algebraMap R (Localization.AtPrime p))) (algebraMap R (Localization.AtPrime p))
      Ideal.le_comap_map) x
    change ConeSymmetric.BundleCycles.normalConeSymmetricMap _ (ρ p x) = 0
    exact hn.trans (by simp only [RingHom.comp_apply, hx, map_zero])

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeLocalDetection.BundleCycles
