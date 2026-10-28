import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Charts

/-! # Localization -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Localization.Construction

noncomputable section

/-! Localization and the open complement maps of the affine blowup for Blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The chart embedding gives the localized base its natural chart-algebra structure. -/
instance blowupChartLocalizationAlgebra (a : I) :
    Algebra (Charts.Construction.blowupChart I a) (Localization.Away a.val) :=
  (Charts.Construction.blowupChartToLocalization I a).toAlgebra

/-- Inverting `a` in the chart `R[I/a]` gives precisely `R[1/a]`. -/
instance blowupChartLocalization_isLocalization (a : I) :
    IsLocalization.Away (Charts.Construction.blowupChartConstants I a a.val) (Localization.Away a.val) := by
  refine IsLocalization.Away.mk (Charts.Construction.blowupChartConstants I a a.val) ?_ ?_ ?_
  · change IsUnit (Charts.Construction.blowupChartToLocalization I a (Charts.Construction.blowupChartConstants I a a.val))
    rw [Charts.Construction.blowupChartToLocalization_constants]
    exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a.val) a.val
  · intro z
    obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj (S := Localization.Away a.val) a.val z
    refine ⟨n, Charts.Construction.blowupChartConstants I a r, ?_⟩
    change z * Charts.Construction.blowupChartToLocalization I a (Charts.Construction.blowupChartConstants I a a.val) ^ n =
      Charts.Construction.blowupChartToLocalization I a (Charts.Construction.blowupChartConstants I a r)
    simpa only [Charts.Construction.blowupChartToLocalization_constants] using hr
  · intro x y hxy
    have h : x = y := Charts.Construction.blowupChartToLocalization_injective I a hxy
    exact ⟨0, by simpa using h⟩

/-- The standard affine localization morphism of the base scheme. -/
def baseLocalizationMap (a : R) : Spec (.of (Localization.Away a)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a)))

instance baseLocalizationMap_isOpenImmersion (a : R) :
    IsOpenImmersion (baseLocalizationMap a) :=
  IsOpenImmersion.of_isLocalization a

/-- The open map from the complement of `a = 0` into the affine blowup. -/
def affineBlowupComplementMap (a : I) :
    Spec (.of (Localization.Away a.val)) ⟶ ReesGrading.Construction.affineBlowup I :=
  Spec.map (CommRingCat.ofHom (Charts.Construction.blowupChartToLocalization I a)) ≫
    Proj.awayι (ReesGrading.Construction.reesGrade I) (Charts.Construction.reesGenerator I a) (Charts.Construction.reesGenerator_mem I a) (by decide)

instance affineBlowupComplementMap_isOpenImmersion (a : I) :
    IsOpenImmersion (affineBlowupComplementMap I a) := by
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Charts.Construction.blowupChartToLocalization I a))) :=
    IsOpenImmersion.of_isLocalization (Charts.Construction.blowupChartConstants I a a.val)
  unfold affineBlowupComplementMap
  infer_instance

/-- The open complement map lies over the original affine base. -/
theorem affineBlowupComplementMap_over (a : I) :
    affineBlowupComplementMap I a ≫ ReesGrading.Construction.affineBlowupToSpec I = baseLocalizationMap a.val := by
  rw [affineBlowupComplementMap, Category.assoc, Charts.Construction.affineBlowup_chart_structureMap,
    ← Spec.map_comp]
  unfold baseLocalizationMap
  congr 1
  ext r
  exact Charts.Construction.blowupChartToLocalization_constants I a r

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Localization.Construction
