import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationStalks

/-! # Localization Rational Order -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationRationalOrder.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual rational orders under arbitrary ring localization

The localization morphism identifies the generic fields and the local
rings at corresponding points. Consequently it preserves the existing
integer rational order, including poles. The complete finite principal
divisor restricts by the actual injective map on spectrum points.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
variable [Algebra R S] (M : Submonoid R) [IsLocalization M S]

include M

theorem localizationAlgebraMap_injective : Function.Injective (algebraMap R S) := by
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
  exact (RingHom.injective_iff_ker_eq_bot (algebraMap R S)).mp (localizationAlgebraMap_injective R S M)

def localizationFunctionFieldMap : (Spec (.of R)).functionField ⟶ (Spec (.of S)).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Spec.map (CommRingCat.ofHom (algebraMap R S))) (localization_genericPoint R S M)

instance localizationFunctionFieldMap_isIso : IsIso (localizationFunctionFieldMap R S M) := by
  let := LocalizationStalks.BundleCycles.localizationStalkMap_isIso R S M (genericPoint (Spec (.of S)))
  unfold localizationFunctionFieldMap Cycles.Functoriality.FunctionFields.Construction.genericFieldMap
  infer_instance

def localizationFunctionFieldIso : (Spec (.of R)).functionField ≅ (Spec (.of S)).functionField :=
  asIso (localizationFunctionFieldMap R S M)

variable [IsNoetherianRing R] [IsNoetherianRing S]

theorem ord_localization (g : (Spec (.of R)).functionField) (x : Spec (.of S)) :
    (Spec (.of S)).ord (localizationFunctionFieldMap R S M g) x =
      (Spec (.of R)).ord g ((Spec.map (CommRingCat.ofHom (algebraMap R S))) x) := by
  let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
  have hc : coheight (i x) = coheight x := LocalizationStalks.BundleCycles.localization_coheight R S M x
  by_cases hx : coheight x = 1
  · let : Ring.KrullDimLE 1 ((Spec (.of S)).presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    let : Ring.KrullDimLE 1 ((Spec (.of R)).presheaf.stalk (i x)) := krullDimLE_of_coheight_le (hc.trans hx).le
    let : IsIso (i.stalkMap x) := LocalizationStalks.BundleCycles.localizationStalkMap_isIso R S M x
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx, Scheme.ord_eq_ordHom_of_coheight_eq_one (hc.trans hx)]
    exact congrArg (fun z : WithZero (Multiplicative ℤ) => Multiplicative.toAdd (z.unzeroD 1))
      (RationalDivisorRestriction.BundleCycles.ringOrderFrac_equiv (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv
        (localizationFunctionFieldIso R S M).commRingCatIsoToRingEquiv
        (RationalDivisorRestriction.BundleCycles.genericFieldMap_stalk i (localization_genericPoint R S M) x) g)
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hx (hc.symm.trans h))]

theorem principalDivisor_localization (g : (Spec (.of R)).functionField) :
    Finsupp.comapDomain (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Ord.BundleCycles.principalDivisor (Spec (.of R)) g)
      (PrimeSpectrum.localization_comap_injective S M).injOn =
      Ord.BundleCycles.principalDivisor (Spec (.of S)) (localizationFunctionFieldMap R S M g) := by
  ext x
  exact (ord_localization R S M g x).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationRationalOrder.BundleCycles
