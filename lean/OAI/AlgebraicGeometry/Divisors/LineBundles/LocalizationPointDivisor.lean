import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationRationalOrder

/-! # Localization Point Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationPointDivisor.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual point-divisor equations on a localization lift to rational functions before localization -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R S : Type) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    [IsNoetherianRing R] [IsNoetherianRing S]

include M

theorem localizationPointDivisor_lift (p : Spec (.of S)) (a : (Spec (.of S)).functionField)
    (ha : a ≠ 0) (hdiv : RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (.of S)) a = Finsupp.single p 1) :
    ∃ g : (Spec (.of R)).functionField, g ≠ 0 ∧ ∀ q : Spec (.of S),
      ((Spec (.of R)).ord g ((Spec.map (CommRingCat.ofHom (algebraMap R S))) q) : ℚ) =
        Finsupp.single p 1 q := by
  let e := LocalizationRationalOrder.BundleCycles.localizationFunctionFieldIso R S M
  let g := e.inv a
  have hg : g ≠ 0 := (map_ne_zero_iff _ e.symm.commRingCatIsoToRingEquiv.injective).mpr ha
  refine ⟨g, hg, ?_⟩
  intro q
  have h : LocalizationRationalOrder.BundleCycles.localizationFunctionFieldMap R S M g = a := Iso.inv_hom_id_apply e a
  have hord := LocalizationRationalOrder.BundleCycles.ord_localization R S M g q
  rw [h] at hord
  exact (congrArg (fun n : ℤ => (n : ℚ)) hord).symm.trans (congrArg (fun z => z q) hdiv)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationPointDivisor.BundleCycles
