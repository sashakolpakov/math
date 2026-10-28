import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Equalizer

/-! # Crystalline Equalizer -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineEqualizer

noncomputable section

/-!
# IntegralComparison: equalizers in the small crystalline category

Parallel small-site morphisms agree on the closed subschemes, since these
are open subschemes of X. The constructed divided-power relation quotient
therefore gives their actual equalizer and the inclusion preserves it.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable {U V : Crystalline.Site.AffineThickening p B J δ f} (α β : U ⟶ V)

lemma quotient_maps_equal : Crystalline.Site.AffineThickening.quotientMap U V α.ringMap =
    Crystalline.Site.AffineThickening.quotientMap U V β.ringMap := by
  have h := (cancel_mono V.openMap).mp (α.overX.trans β.overX.symm)
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

abbrev object : Crystalline.Site.AffineThickening p B J δ f :=
  Crystalline.RelationQuotient.smallObject U
    (Crystalline.Equalizer.relations (BigCrystallineSite.fromSmall.map α) (BigCrystallineSite.fromSmall.map β))
    (Crystalline.Equalizer.relations_subset (BigCrystallineSite.fromSmall.map α) (BigCrystallineSite.fromSmall.map β)
      (quotient_maps_equal α β))

def hom : object α β ⟶ U where
  ringMap := (Crystalline.Equalizer.hom (BigCrystallineSite.fromSmall.map α) (BigCrystallineSite.fromSmall.map β)
    (quotient_maps_equal α β)).ringMap
  overBase := rfl
  overX := rfl

lemma condition : CrystallineEqualizer.hom α β ≫ α = CrystallineEqualizer.hom α β ≫ β := by
  apply BigCrystallineSite.fromSmall.map_injective
  exact Crystalline.Equalizer.condition (BigCrystallineSite.fromSmall.map α) (BigCrystallineSite.fromSmall.map β)
    (quotient_maps_equal α β)

def fork : Fork α β := Fork.ofι (CrystallineEqualizer.hom α β) (condition α β)

def isEqualizer : IsLimit (fork α β) :=
  isLimitOfIsLimitForkMap BigCrystallineSite.fromSmall (condition α β)
    (Crystalline.Equalizer.isEqualizer (BigCrystallineSite.fromSmall.map α) (BigCrystallineSite.fromSmall.map β)
      (quotient_maps_equal α β))

instance hasEqualizer : HasEqualizer α β := HasLimit.mk ⟨fork α β, isEqualizer α β⟩

instance hasEqualizers : HasEqualizers (Crystalline.Site.AffineThickening p B J δ f) :=
  hasEqualizers_of_hasLimit_parallelPair _

instance inclusion_preserves_equalizer : PreservesLimit (parallelPair α β) BigCrystallineSite.fromSmall :=
  preservesLimit_of_preserves_limit_cone (isEqualizer α β)
    ((isLimitMapConeForkEquiv BigCrystallineSite.fromSmall (condition α β)).symm
      (Crystalline.Equalizer.isEqualizer (BigCrystallineSite.fromSmall.map α) (BigCrystallineSite.fromSmall.map β)
        (quotient_maps_equal α β)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineEqualizer
