import OAI.AlgebraicGeometry.Divisors.LineBundles.FlatExtendedPrimeOrder
import OAI.AlgebraicGeometry.Divisors.LineBundles.FlatMorphismOrder

/-! # Extended Prime Stalk -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ExtendedPrimeStalk.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual affine stalk map at an extended prime -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

theorem affineExtendedPrime_stalk_maximalIdeal (P : Spec (CommRingCat.of S))
    (hP : (P.asIdeal.under R).map (algebraMap R S) = P.asIdeal) :
    (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))) P))).map
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap P).hom =
          IsLocalRing.maximalIdeal ((Spec (CommRingCat.of S)).presheaf.stalk P) := by
  let : P.asIdeal.IsPrime := (show PrimeSpectrum S from P).isPrime
  let f : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  let p : Spec (CommRingCat.of R) := (Spec.map f) P
  let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
  let eR := Spec.stalkIso (CommRingCat.of R) p
  let eS := Spec.stalkIso (CommRingCat.of S) P
  let l := Localization.localRingHom p.asIdeal P.asIdeal f.hom rfl
  have hlocal : (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).map l =
      IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) :=
    FlatExtendedPrimeOrder.BundleCycles.extendedPrimeLocalMap_maximalIdeal p.asIdeal P.asIdeal rfl hP
  have he := congrArg CommRingCat.Hom.hom (Scheme.localRingHom_comp_stalkIso f P)
  apply (congrArg (fun t : ((Spec (CommRingCat.of R)).presheaf.stalk p) →+*
    ((Spec (CommRingCat.of S)).presheaf.stalk P) =>
      (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk p)).map t) he).symm.trans
  change (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk p)).map
    (eS.inv.hom.comp (l.comp eR.hom.hom)) = _
  rw [← Ideal.map_map, ← Ideal.map_map]
  have hR : (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk
      ((Spec.map f) P))).map eR.hom.hom = IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) :=
    IsLocalRing.map_ringEquiv_maximalIdeal eR.commRingCatIsoToRingEquiv
  rw [hR, hlocal]
  exact IsLocalRing.map_ringEquiv_maximalIdeal eS.symm.commRingCatIsoToRingEquiv

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ExtendedPrimeStalk.BundleCycles
