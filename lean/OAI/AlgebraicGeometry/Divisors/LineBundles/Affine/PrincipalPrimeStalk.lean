import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroPrime

/-! # Principal Prime Stalk -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrincipalPrimeStalk.BundleCycles

noncomputable section

/-! # LineBundleCycles: a principal prime generator generates the actual affine stalk maximal ideal -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affinePrincipalPrime_stalk_maximalIdeal {R : Type} [CommRing R]
    (p : Spec (.of R)) (a : R) (hp : p.asIdeal = Ideal.span {a}) :
    Ideal.span {(Spec (.of R)).presheaf.germ ⊤ p (by trivial) ((Scheme.ΓSpecIso (.of R)).inv a)} =
      IsLocalRing.maximalIdeal ((Spec (.of R)).presheaf.stalk p) := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
  let e := Spec.stalkIso (.of R) p
  have hg := ConcreteCategory.congr_hom (Spec.germ_stalkMapIso_hom (R := .of R) p)
    ((Scheme.ΓSpecIso (.of R)).inv a)
  change e.hom ((Spec (.of R)).presheaf.germ ⊤ p (by trivial) ((Scheme.ΓSpecIso (.of R)).inv a)) =
    algebraMap R (Localization.AtPrime p.asIdeal) ((Scheme.ΓSpecIso (.of R)).hom ((Scheme.ΓSpecIso (.of R)).inv a)) at hg
  rw [Iso.inv_hom_id_apply] at hg
  have hL : (Ideal.span {(Spec (.of R)).presheaf.germ ⊤ p (by trivial) ((Scheme.ΓSpecIso (.of R)).inv a)}).map e.hom.hom =
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) := by
    rw [Ideal.map_span, Set.image_singleton, hg, ← Set.image_singleton, ← Ideal.map_span, ← hp]
    exact Localization.AtPrime.map_eq_maximalIdeal
  have hM : (IsLocalRing.maximalIdeal ((Spec (.of R)).presheaf.stalk p)).map e.hom.hom =
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) :=
    IsLocalRing.map_ringEquiv_maximalIdeal e.commRingCatIsoToRingEquiv
  have h := congrArg (Ideal.comap e.hom.hom) (hL.trans hM.symm)
  have he : Function.Bijective e.hom.hom := e.commRingCatIsoToRingEquiv.bijective
  rw [Ideal.comap_map_of_bijective e.hom.hom he,
    Ideal.comap_map_of_bijective e.hom.hom he] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrincipalPrimeStalk.BundleCycles
