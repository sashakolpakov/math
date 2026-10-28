import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.SectionCotangent
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Algebra

/-! # Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Section.Localization.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual localizations of a ring section and its kernel -/

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A] (p : Ideal A) [p.IsPrime]

omit [p.IsPrime] in
theorem sectionPrime_comap :
    (p.comap (algebraMap B A)).comap (algebraMap A B) = p := by
  ext a
  change algebraMap B A (algebraMap A B a) ∈ p ↔ a ∈ p
  rw [← IsScalarTower.algebraMap_apply A B A]
  rfl

def localizedSectionLift : Localization.AtPrime p →+* Localization.AtPrime (p.comap (algebraMap B A)) :=
  Localization.localRingHom p (p.comap (algebraMap B A)) (algebraMap A B) (sectionPrime_comap A B p).symm

def localizedSectionQuotient : Localization.AtPrime (p.comap (algebraMap B A)) →+* Localization.AtPrime p :=
  Localization.localRingHom (p.comap (algebraMap B A)) p (algebraMap B A) rfl

theorem localizedSectionLift_algebraMap (a : A) :
    localizedSectionLift A B p (algebraMap A (Localization.AtPrime p) a) =
      algebraMap B (Localization.AtPrime (p.comap (algebraMap B A))) (algebraMap A B a) :=
  Localization.localRingHom_to_map _ _ _ _ a

omit [Algebra A B] [IsScalarTower A B A] in
theorem localizedSectionQuotient_algebraMap (b : B) :
    localizedSectionQuotient A B p (algebraMap B (Localization.AtPrime (p.comap (algebraMap B A))) b) =
      algebraMap A (Localization.AtPrime p) (algebraMap B A b) :=
  Localization.localRingHom_to_map _ _ _ _ b

theorem localizedSection_retraction :
    (localizedSectionQuotient A B p).comp (localizedSectionLift A B p) = RingHom.id (Localization.AtPrime p) := by
  apply IsLocalization.ringHom_ext p.primeCompl
  apply RingHom.ext
  intro a
  change localizedSectionQuotient A B p (localizedSectionLift A B p (algebraMap A (Localization.AtPrime p) a)) = _
  rw [localizedSectionLift_algebraMap, localizedSectionQuotient_algebraMap,
    ← IsScalarTower.algebraMap_apply A B A]
  rfl

theorem localizedSectionQuotient_ker :
    RingHom.ker (localizedSectionQuotient A B p) =
      (RingHom.ker (algebraMap B A)).map (algebraMap B (Localization.AtPrime (p.comap (algebraMap B A)))) := by
  have h := Ideal.map_primeCompl_comap_of_surjective (algebraMap B A) (Smooth.SectionCotangent.BundleCycles.algebraSection_surjective A B) p
  exact IsLocalization.ker_map (S := Localization.AtPrime (p.comap (algebraMap B A)))
    (Localization.AtPrime p) (algebraMap B A) h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Section.Localization.BundleCycles
