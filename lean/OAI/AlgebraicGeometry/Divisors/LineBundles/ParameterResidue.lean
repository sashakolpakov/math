import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Place
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ResidueDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationStalks
import OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalStalk

/-! # Parameter Residue -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ParameterResidue.BundleCycles.ParameterResidueDegree

noncomputable section

/-! The zero place has residue degree one over the ground field in the
native scheme pushforward, including the localization and residue maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

universe u

theorem localization_residueDegree (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] (q : Spec (.of S)) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).residueDegree q = 1 := by
  let := LocalizationStalks.BundleCycles.localizationStalkMap_isIso R S M q
  exact BirationalStalk.BundleCycles.BirationalStalkResidueDegree.residueDegree_of_isIso_stalkMap _ q

theorem residueDegree_over_field (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (a : PrimeSpectrum A) :
    (Spec.map (CommRingCat.ofHom (algebraMap k A))).residueDegree a =
      Module.finrank k a.asIdeal.ResidueField := by
  let p := a.asIdeal.under k
  let := Localization.AtPrime.algebraOfLiesOver p a.asIdeal
  rw [Affine.ResidueDegree.BundleCycles.affineResidueDegree_eq_inertiaDeg, Ideal.inertiaDeg_def]
  have he : Module.finrank k p.ResidueField = 1 := by
    rw [← (p.algEquivResidueFieldOfField).toLinearEquiv.finrank_eq, Module.finrank_self]
  have ht := Module.finrank_mul_finrank k p.ResidueField a.asIdeal.ResidueField
  simpa only [he, one_mul] using ht

theorem zero_place_residueDegree (k : Type u) [Field k] :
    (Spec.map (CommRingCat.ofHom (algebraMap k (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k)))).residueDegree
      (IsLocalRing.closedPoint (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k)) = 1 := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k)))
  let f := Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))
  have hc : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hp : j (IsLocalRing.closedPoint (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k)) =
      (⟨LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.zeroIdeal k, inferInstance⟩ : PrimeSpectrum (Polynomial k)) := by
    apply PrimeSpectrum.ext
    exact IsLocalization.AtPrime.under_maximalIdeal (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.zeroIdeal k)
  let a : Spec (.of (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k)) := IsLocalRing.closedPoint (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k)
  have hj : j.residueDegree a = 1 :=
    localization_residueDegree (Polynomial k) (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.zeroIdeal k).primeCompl a
  have hf : f.residueDegree (j a) = 1 :=
    (congrArg (fun z : Spec (.of (Polynomial k)) => f.residueDegree z) hp).trans
      ((residueDegree_over_field k (Polynomial k) ⟨LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.zeroIdeal k, inferInstance⟩).trans
        (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.residue_finrank k))
  have he := congrArg (fun t : Spec (.of (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k)) ⟶ Spec (.of k) => t.residueDegree a) hc
  exact he.symm.trans ((IntersectionTheory.ProjectionFormula.CyclePushforward.residueDegree_comp j f a).trans (by rw [hj, hf, mul_one]))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ParameterResidue.BundleCycles.ParameterResidueDegree
