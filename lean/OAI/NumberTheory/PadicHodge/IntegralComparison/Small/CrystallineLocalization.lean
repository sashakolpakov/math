import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Covers

/-! # Crystalline Localization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineLocalization

noncomputable section

/-!
# IntegralComparison: principal localizations in the small crystalline site

The same divided-power localization construction stays in the small site:
its closed subscheme remains an open subscheme of X. Its principal covering
families are coverings for the original small-site topology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}

instance closedMap_open (U : BigCrystallineSite.Object p B J δ f) (r : U.ring) : IsOpenImmersion (Crystalline.Localization.closedMap U r) :=
  MorphismProperty.of_isPullback (Crystalline.Localization.closed_cartesian U r).flip inferInstance

abbrev smallOfBig (U : BigCrystallineSite.Object p B J δ f) [IsOpenImmersion U.mapToX] :
    Crystalline.Site.AffineThickening p B J δ f where
  ring := U.ring
  base := U.base
  ideal := U.ideal
  dividedPowers := U.dividedPowers
  baseCompatible := U.baseCompatible
  primeNilpotent := U.primeNilpotent
  nilIdeal := U.nilIdeal
  openMap := U.mapToX
  isOpenImmersion := inferInstance
  overBase := U.overBase

lemma fromSmall_smallOfBig (U : BigCrystallineSite.Object p B J δ f) [IsOpenImmersion U.mapToX] :
    BigCrystallineSite.fromSmall.obj (smallOfBig U) = U := rfl

variable (U : Crystalline.Site.AffineThickening p B J δ f) (r : U.ring)

instance localized_map_open : IsOpenImmersion (Crystalline.Localization.object (BigCrystallineSite.fromSmall.obj U) r).mapToX := by
  let q : Spec (CommRingCat.of (Crystalline.Localization.Ring (BigCrystallineSite.fromSmall.obj U) r ⧸ Crystalline.Localization.ideal (BigCrystallineSite.fromSmall.obj U) r)) ⟶
      Spec (CommRingCat.of (U.ring ⧸ U.ideal)) := Crystalline.Localization.closedMap (BigCrystallineSite.fromSmall.obj U) r
  have hq : IsOpenImmersion q := closedMap_open (BigCrystallineSite.fromSmall.obj U) r
  exact @IsOpenImmersion.comp _ _ _ q U.openMap hq U.isOpenImmersion

abbrev smallObject : Crystalline.Site.AffineThickening p B J δ f := smallOfBig (Crystalline.Localization.object (BigCrystallineSite.fromSmall.obj U) r)

def smallHom : smallObject U r ⟶ U where
  ringMap := Crystalline.Localization.localizationDP (BigCrystallineSite.fromSmall.obj U) r
  overBase := rfl
  overX := rfl

lemma fromSmall_smallHom : BigCrystallineSite.fromSmall.map (smallHom U r) = Crystalline.Localization.hom (BigCrystallineSite.fromSmall.obj U) r := by
  apply BigCrystallineSite.Object.Hom.ext
  rfl

variable {ι : Type v} (a : ι → U.ring)

def smallPresieve : Presieve U :=
  Presieve.ofArrows (fun i => smallObject U (a i)) (fun i => smallHom U (a i))

lemma small_covering (ha : Ideal.span (Set.range a) = ⊤) :
    smallPresieve U a ∈ Crystalline.Site.AffineThickening.precoverage U := by
  have h := (CrystallinePrincipal.Covers.covering (BigCrystallineSite.fromSmall.obj U) a ha).1
  change (Presieve.ofArrows _ _).map Crystalline.Site.AffineThickening.ambient ∈ Scheme.precoverage IsOpenImmersion _
  change (Presieve.ofArrows _ _).map BigCrystallineSite.Object.ambient ∈ Scheme.precoverage IsOpenImmersion _ at h
  rw [Presieve.map_ofArrows] at h ⊢
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineLocalization
