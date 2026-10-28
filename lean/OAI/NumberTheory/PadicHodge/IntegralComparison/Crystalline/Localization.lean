import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Coverings
import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Localization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.QuotientPullback

/-! # Localization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization

noncomputable section

/-!
# IntegralComparison: principal open crystalline thickenings

Localizing an ambient divided-power ring gives an actual crystalline
object. Its closed subscheme is the base change of the original closed
subscheme, with a proved pullback square in the category of all schemes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable (U : BigCrystallineSite.Object p B J δ f) (r : U.ring)

abbrev Ring := Localization.Away r

abbrev ideal : Ideal (Ring U r) := U.ideal.map (algebraMap U.ring (Ring U r))

abbrev dividedPowers :=
  DividedPower.Localization.dividedPowers U.dividedPowers (Submonoid.powers r) (Ring U r)

def baseMap : B →+* Ring U r := (algebraMap U.ring (Ring U r)).comp U.base

def localizationDP : DividedPowers.DPMorphism U.dividedPowers (Crystalline.Localization.dividedPowers U r) :=
  DividedPower.Localization.localizationMap U.dividedPowers (Submonoid.powers r) (Ring U r)

def closedMap : Spec (CommRingCat.of (Ring U r ⧸ Crystalline.Localization.ideal U r)) ⟶
    Spec (CommRingCat.of (U.ring ⧸ U.ideal)) :=
  Spec.map (CommRingCat.ofHom (IntegralComparison.Quotient.QuotientPullback.residueMap U.ideal
    (algebraMap U.ring (Ring U r))))

lemma primeNilpotent : IsNilpotent (p : Ring U r) := by
  obtain ⟨n, hn⟩ := U.primeNilpotent
  refine ⟨n, ?_⟩
  rw [← map_natCast (algebraMap U.ring (Ring U r)) p, ← map_pow, hn, map_zero]

lemma nilIdeal : ∀ x ∈ Crystalline.Localization.ideal U r, IsNilpotent x := by
  intro x hx
  obtain ⟨a, s, rfl⟩ :=
    DividedPower.Localization.ideal_fraction (Submonoid.powers r) (Ring U r) hx
  obtain ⟨n, hn⟩ := U.nilIdeal a a.property
  refine ⟨n, ?_⟩
  rw [IsLocalization.mk'_eq_mul_mk'_one, mul_pow, ← map_pow, hn, map_zero, zero_mul]

lemma closed_cartesian : IsPullback (closedMap U r)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Crystalline.Localization.ideal U r))))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk U.ideal)))
    (Spec.map (CommRingCat.ofHom (algebraMap U.ring (Ring U r)))) :=
  IntegralComparison.Quotient.QuotientPullback.schemePullback U.ideal (algebraMap U.ring (Ring U r))

abbrev object : BigCrystallineSite.Object p B J δ f where
  ring := CommRingCat.of (Ring U r)
  base := baseMap U r
  ideal := Crystalline.Localization.ideal U r
  dividedPowers := Crystalline.Localization.dividedPowers U r
  baseCompatible := (localizationDP U r).isDPMorphism.comp _ U.baseCompatible
  primeNilpotent := Crystalline.Localization.primeNilpotent U r
  nilIdeal := Crystalline.Localization.nilIdeal U r
  mapToX := closedMap U r ≫ U.mapToX
  overBase := by
    rw [Category.assoc, U.overBase, ← Category.assoc, (closed_cartesian U r).w,
      Category.assoc, ← Spec.map_comp]
    rfl

def hom : object U r ⟶ U where
  ringMap := localizationDP U r
  overBase := rfl
  overX := rfl

lemma hom_cartesian : BigCrystallineSite.Object.Cartesian (hom U r) := closed_cartesian U r

instance hom_open : IsOpenImmersion (BigCrystallineSite.Object.ambient.map (hom U r)) :=
  inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap U.ring (Localization.Away r)))))

lemma hom_range : (BigCrystallineSite.Object.ambient.map (hom U r)).opensRange = PrimeSpectrum.basicOpen r :=
  Scheme.Hom.opensRange_localizationAway r

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization
