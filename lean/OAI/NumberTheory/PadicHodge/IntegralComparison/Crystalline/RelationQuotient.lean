import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Relations
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineLocalization

/-! # Relation Quotient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelationQuotient

noncomputable section

/-!
# IntegralComparison: quotienting crystalline thickenings by divided-power relations

Relations inside the divided-power ideal preserve the original closed
subscheme. The quotient is an actual crystalline object, and it stays in
the small site whenever the original object belongs to the small site.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable (U : BigCrystallineSite.Object p B J δ f) (S : Set U.ring) (hS : S ⊆ U.ideal)

abbrev Ring := U.ring ⧸ DividedPower.Relations.relationIdeal U.dividedPowers S

abbrev quotientRingMap : U.ring →+* Ring U S :=
  Ideal.Quotient.mk (DividedPower.Relations.relationIdeal U.dividedPowers S)

abbrev ideal := U.ideal.map (quotientRingMap U S)

abbrev dividedPowers := DividedPower.Relations.dividedPowers U.dividedPowers S hS

def quotientDP : DividedPowers.DPMorphism U.dividedPowers (RelationQuotient.dividedPowers U S hS) :=
  DividedPower.Relations.quotientMap U.dividedPowers S hS

def closedRingMap : U.ring ⧸ U.ideal →+* Ring U S ⧸ RelationQuotient.ideal U S :=
  IntegralComparison.Quotient.QuotientPullback.residueMap U.ideal (quotientRingMap U S)

include hS in
lemma closedRingMap_eq : closedRingMap U S =
    (DividedPower.Relations.residueEquiv U.dividedPowers S hS).symm.toRingHom := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

def closedMap : Spec (CommRingCat.of (Ring U S ⧸ RelationQuotient.ideal U S)) ⟶
    Spec (CommRingCat.of (U.ring ⧸ U.ideal)) := Spec.map (CommRingCat.ofHom (closedRingMap U S))

include hS in
lemma closedMap_isIso : IsIso (closedMap U S) := by
  unfold closedMap
  rw [closedRingMap_eq U S hS]
  exact inferInstanceAs (IsIso (Spec.map
    (DividedPower.Relations.residueEquiv U.dividedPowers S hS).toCommRingCatIso.inv))

lemma closed_cartesian : IsPullback (closedMap U S)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RelationQuotient.ideal U S))))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk U.ideal)))
    (Spec.map (CommRingCat.ofHom (quotientRingMap U S))) :=
  IntegralComparison.Quotient.QuotientPullback.schemePullback U.ideal (quotientRingMap U S)

abbrev object : BigCrystallineSite.Object p B J δ f where
  ring := CommRingCat.of (Ring U S)
  base := (quotientRingMap U S).comp U.base
  ideal := RelationQuotient.ideal U S
  dividedPowers := RelationQuotient.dividedPowers U S hS
  baseCompatible := (quotientDP U S hS).isDPMorphism.comp _ U.baseCompatible
  primeNilpotent := by simpa only [map_natCast] using U.primeNilpotent.map (quotientRingMap U S)
  nilIdeal := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective (quotientRingMap U S) Ideal.Quotient.mk_surjective).mp hx
    exact (U.nilIdeal a ha).map (quotientRingMap U S)
  mapToX := closedMap U S ≫ U.mapToX
  overBase := by
    rw [Category.assoc, U.overBase, ← Category.assoc,
      (closed_cartesian U S).w,
      Category.assoc, ← Spec.map_comp]
    rfl

def hom : object U S hS ⟶ U where
  ringMap := quotientDP U S hS
  overBase := rfl
  overX := rfl

instance quotient_open [IsOpenImmersion U.mapToX] : IsOpenImmersion (object U S hS).mapToX := by
  have : IsIso (closedMap U S) := closedMap_isIso U S hS
  change IsOpenImmersion (closedMap U S ≫ U.mapToX)
  infer_instance

abbrev smallObject (U : Site.AffineThickening p B J δ f)
    (S : Set U.ring) (hS : S ⊆ U.ideal) : Site.AffineThickening p B J δ f := by
  have : IsOpenImmersion (BigCrystallineSite.fromSmall.obj U).mapToX := U.isOpenImmersion
  have : IsOpenImmersion (object (BigCrystallineSite.fromSmall.obj U) S hS).mapToX := quotient_open (BigCrystallineSite.fromSmall.obj U) S hS
  exact Small.CrystallineLocalization.smallOfBig (object (BigCrystallineSite.fromSmall.obj U) S hS)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelationQuotient
