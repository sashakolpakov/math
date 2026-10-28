import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizationStalks
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.DivisorRestriction

/-! # Localization Divisor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizationDivisor

noncomputable section

/-! Rational principal divisors restrict through arbitrary localizations,
not only open immersions. This supplies the divisor comparison between a
normalization chart and its localization over a point of the base. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.DivisorRestriction OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizationStalks

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] (M : Submonoid R) [IsLocalization M S]

include M

theorem localization_algebraMap_injective : Function.Injective (algebraMap R S) := by
  apply IsLocalization.injective S (M := M)
  intro m hm
  apply mem_nonZeroDivisors_of_ne_zero
  intro hz
  have hu := IsLocalization.map_units S (⟨m, hm⟩ : M)
  change IsUnit (algebraMap R S m) at hu
  rw [hz, map_zero] at hu
  exact not_isUnit_zero hu

theorem localization_genericPoint :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) (genericPoint (Spec (.of S))) =
      genericPoint (Spec (.of R)) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  exact (RingHom.injective_iff_ker_eq_bot (algebraMap R S)).mp
    (localization_algebraMap_injective R S M)

def localizationFieldMap : (Spec (.of R)).functionField ⟶ (Spec (.of S)).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (localization_genericPoint R S M)

instance : IsIso (localizationFieldMap R S M) := by
  let := LocalizationStalks.localization_stalkMap_isIso R S M (genericPoint (Spec (.of S)))
  unfold localizationFieldMap Cycles.Functoriality.FunctionFields.Construction.genericFieldMap
  infer_instance

def localizationFieldIso : (Spec (.of R)).functionField ≅ (Spec (.of S)).functionField :=
  asIso (localizationFieldMap R S M)

variable [IsNoetherianRing R] [IsNoetherianRing S]

theorem ord_localization (f : (Spec (.of R)).functionField) (x : Spec (.of S)) :
    (Spec (.of S)).ord (localizationFieldMap R S M f) x =
      (Spec (.of R)).ord f ((Spec.map (CommRingCat.ofHom (algebraMap R S))) x) := by
  let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
  have hc : coheight (i x) = coheight x := LocalizationStalks.localization_coheight R S M x
  by_cases hx : coheight x = 1
  · let : Ring.KrullDimLE 1 ((Spec (.of S)).presheaf.stalk x) :=
      krullDimLE_of_coheight_le hx.le
    let : Ring.KrullDimLE 1 ((Spec (.of R)).presheaf.stalk (i x)) :=
      krullDimLE_of_coheight_le (hc.trans hx).le
    let : IsIso (i.stalkMap x) := LocalizationStalks.localization_stalkMap_isIso R S M x
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx,
      Scheme.ord_eq_ordHom_of_coheight_eq_one (hc.trans hx)]
    exact congrArg WithZero.log (OrderQuotientTransport.ordFrac_equiv
      (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv
      (localizationFieldIso R S M).commRingCatIsoToRingEquiv
      (Divisor.DivisorRestriction.genericFieldMap_stalk i (localization_genericPoint R S M) x) f)
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hx (hc.symm.trans h))]

theorem principalDivisor_localization (f : (Spec (.of R)).functionField) :
    Finsupp.comapDomain (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Divisors.LineBundles.Ord.BundleCycles.principalDivisor (Spec (.of R)) f)
      (PrimeSpectrum.localization_comap_injective S M).injOn =
        Divisors.LineBundles.Ord.BundleCycles.principalDivisor (Spec (.of S)) (localizationFieldMap R S M f) := by
  ext x
  exact (ord_localization R S M f x).symm

theorem rationalPrincipalDivisor_localization (f : (Spec (.of R)).functionField) :
    Finsupp.comapDomain (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Affine.DivisorNorm.rationalPrincipalDivisor (Spec (.of R)) f)
      (PrimeSpectrum.localization_comap_injective S M).injOn =
        Affine.DivisorNorm.rationalPrincipalDivisor (Spec (.of S)) (localizationFieldMap R S M f) := by
  ext x
  exact congrArg (fun n : ℤ => (n : ℚ)) (ord_localization R S M f x).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizationDivisor
