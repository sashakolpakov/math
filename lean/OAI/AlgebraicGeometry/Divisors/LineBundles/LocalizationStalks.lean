import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction
import Mathlib.RingTheory.Ideal.Height

/-! # Localization Stalks -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationStalks.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual stalks and codimensions under arbitrary localization

Localizing a ring and then localizing at a source prime gives the same
local ring as localizing the original ring at its contracted prime.
The comparison is the actual scheme stalk map, and prime heights are
preserved. These comparisons use the same localization construction as
ProjectionFormula's stalk calculation, with the default elaborator settings.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : Submonoid R) [IsLocalization M S]

include M

theorem localizationLocalRingHom_bijective (q : PrimeSpectrum S) :
    Function.Bijective (Localization.localRingHom (q.asIdeal.under R) q.asIdeal
      (algebraMap R S) rfl) := by
  let A := Localization.AtPrime (q.asIdeal.under R)
  let B := Localization.AtPrime q.asIdeal
  let : IsLocalization.AtPrime B (q.asIdeal.under R) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M B q.asIdeal
  let e : A ≃ₐ[R] B := IsLocalization.algEquiv (q.asIdeal.under R).primeCompl A B
  have he : Localization.localRingHom (q.asIdeal.under R) q.asIdeal
      (algebraMap R S) rfl = e.toRingHom := by
    apply IsLocalization.ringHom_ext (q.asIdeal.under R).primeCompl
    ext r
    change Localization.localRingHom _ _ _ rfl (algebraMap R A r) = e (algebraMap R A r)
    rw [Localization.localRingHom_to_map, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  rw [he]
  exact e.bijective

theorem localizationStalkMap_isIso (q : Spec (CommRingCat.of S)) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap q) := by
  let f : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  let q' : PrimeSpectrum (CommRingCat.of S) := q
  let p := q'.comap f.hom
  let j := CommRingCat.ofHom (Localization.localRingHom p.asIdeal q'.asIdeal f.hom rfl)
  have hj : IsIso j :=
    (ConcreteCategory.isIso_iff_bijective j).mpr (localizationLocalRingHom_bijective R S M q)
  let e := (Spec.stalkIso (CommRingCat.of R) p) ≪≫ (@asIso _ _ _ _ j hj) ≪≫
    (Spec.stalkIso (CommRingCat.of S) q').symm
  have he : e.hom = (Spec.map f).stalkMap q := Scheme.localRingHom_comp_stalkIso f q'
  exact (congrArg (fun k => IsIso k) he).mp e.isIso_hom

theorem localization_coheight (q : Spec (CommRingCat.of S)) :
    Order.coheight ((Spec.map (CommRingCat.ofHom (algebraMap R S))) q) = Order.coheight q := by
  rw [← idealHeight_eq_coheight, ← idealHeight_eq_coheight]
  exact IsLocalization.height_under M q.asIdeal

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationStalks.BundleCycles
