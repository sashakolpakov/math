import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalOpens
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationLift

/-! # Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Functor

noncomputable section

/-!
# IntegralComparison: principal opens inside an actual crystalline slice

Principal localizations define a fully faithful functor to the slice over
the original crystalline object. The factorization and uniqueness proofs
use the constructed divided-power localization maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationLift
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalOpens.Category (Principal)

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} (U : BigCrystallineSite.Object p B J δ f)

def object (r : PrincipalOpens.Category.Principal U.ring) : Over U := Over.mk (Crystalline.Localization.hom U r.function)

theorem hom_ext {T : Over U} {r : PrincipalOpens.Category.Principal U.ring} (a b : T ⟶ object U r) : a = b := by
  apply (Over.forget U).map_injective
  apply (cancel_mono (Crystalline.Localization.hom U r.function)).mp
  exact (Over.w a).trans (Over.w b).symm

theorem unit_of_factor {T : BigCrystallineSite.Object p B J δ f} (β : T ⟶ U) (r : U.ring)
    (a : T ⟶ Crystalline.Localization.object U r) (ha : a ≫ Crystalline.Localization.hom U r = β) :
    IsUnit (β.ringMap r) := by
  have hu := (IsLocalization.Away.algebraMap_isUnit r).map a.ringMap.toRingHom
  have he := congrArg (fun g : T ⟶ U => g.ringMap r) ha
  exact he ▸ hu

def map {r s : PrincipalOpens.Category.Principal U.ring} (a : r ⟶ s) : object U r ⟶ object U s :=
  Over.homMk
    (Crystalline.LocalizationLift.liftHom (Crystalline.Localization.hom U r.function) s.function
      ((PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
        (S := Crystalline.Localization.Ring U r.function)).mp (leOfHom a)))
    (Crystalline.LocalizationLift.liftHom_comp (Crystalline.Localization.hom U r.function) s.function _)

/-- The actual principal-open inclusion in the crystalline slice. -/
def inclusion : PrincipalOpens.Category.Principal U.ring ⥤ Over U where
  obj := object U
  map := Functor.map U
  map_id _ := hom_ext U _ _
  map_comp _ _ := hom_ext U _ _

instance inclusion_faithful : (inclusion U).Faithful where
  map_injective _ := Subsingleton.elim _ _

def preimage {r s : PrincipalOpens.Category.Principal U.ring} (a : object U r ⟶ object U s) : r ⟶ s :=
  homOfLE ((PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
    (S := Crystalline.Localization.Ring U r.function)).mpr (unit_of_factor U (Crystalline.Localization.hom U r.function) s.function a.left (Over.w a)))

instance inclusion_full : (inclusion U).Full where
  map_surjective a := ⟨preimage U a, hom_ext U _ _⟩

def toTerminal (T : Over U) : T ⟶ object U (PrincipalOpens.Category.top U.ring) :=
  Over.homMk (Crystalline.LocalizationLift.liftHom T.hom 1 (by
    change IsUnit (T.hom.ringMap.toRingHom 1)
    rw [map_one]
    exact isUnit_one)) (Crystalline.LocalizationLift.liftHom_comp T.hom 1 _)

/-- The principal unit open remains terminal in the whole crystalline slice. -/
def isTerminal : IsTerminal ((inclusion U).obj (PrincipalOpens.Category.top U.ring)) :=
  IsTerminal.ofUniqueHom (toTerminal U) (fun _ _ => hom_ext U _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Functor
