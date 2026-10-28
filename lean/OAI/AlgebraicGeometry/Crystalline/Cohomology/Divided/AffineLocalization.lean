import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.TensorBaseChange
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.Translations

/-! # Affine Localization -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AffineLocalization.DividedAffineLocalization

noncomputable section

/-!
# Localization under affine divided-coordinate changes

An affine coordinate map factors as coefficient base change followed by
a divided-power translation automorphism. Consequently, when its coefficient
map is a localization, the actual affine divided-coordinate map is also
a localization at the image of the same coefficient submonoid.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R S σ : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (I : Ideal S) (δ : DividedPowers I) (b : σ → S) (hb : ∀ i, b i ∈ I)
  (IR : Ideal R) (δR : DividedPowers IR)
  (hbase : DividedPowers.IsDPMorphism δR δ (algebraMap R S))

local notation "GR" => DividedPowerAlgebra R (σ →₀ R)
local notation "GS" => DividedPowerAlgebra S (σ →₀ S)
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal S σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers S σ I δ

include hbase in
theorem map_factor : AffineMaps.DividedAffineMaps.map R S σ I δ b hb =
    ((Translations.DividedTranslations.algebraEquiv S σ I δ b hb).toAlgHom.restrictScalars R).comp
      (AlgebraBaseChange.DividedAlgebraBaseChange.map R S σ) := by
  have he := AffineMaps.DividedAffineMaps.ringHom_ext_of_coordinate R σ IR δR GS J γ
    (AffineMaps.DividedAffineMaps.map R S σ I δ b hb).toRingHom
    (((Translations.DividedTranslations.algebraEquiv S σ I δ b hb).toAlgHom.restrictScalars R).comp
      (AlgebraBaseChange.DividedAlgebraBaseChange.map R S σ)).toRingHom
    (AffineMaps.DividedAffineMaps.map_isDPMorphism R S σ I δ b hb IR δR hbase)
    ((Translations.DividedTranslations.algebraEquiv_isDPMorphism S σ I δ b hb).comp _
      (FreeRelative.BaseChange.FreeRelativeBaseChange.map_isDPMorphism R S σ IR δR I δ hbase))
    (fun r => (AffineMaps.DividedAffineMaps.map R S σ I δ b hb).commutes r |>.trans
      ((((Translations.DividedTranslations.algebraEquiv S σ I δ b hb).toAlgHom.restrictScalars R).comp
        (AlgebraBaseChange.DividedAlgebraBaseChange.map R S σ)).commutes r).symm)
    (fun i => by
      change AffineMaps.DividedAffineMaps.map R S σ I δ b hb (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) =
        Translations.DividedTranslations.map S σ I δ b hb (AlgebraBaseChange.DividedAlgebraBaseChange.map R S σ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i))
      rw [AlgebraBaseChange.DividedAlgebraBaseChange.map_generator, Translations.DividedTranslations.map_coordinate,
        AffineMaps.DividedAffineMaps.map_coordinate]
      rfl)
  exact AlgHom.ext (RingHom.congr_fun he)

include hbase in
theorem isLocalizationMap (M : Submonoid R) [IsLocalization M S] :
    (Algebra.algebraMapSubmonoid GR M).IsLocalizationMap
      (AffineMaps.DividedAffineMaps.map R S σ I δ b hb) := by
  have hcoef := (FreeDivided.TensorBaseChange.FreeDividedTensorBaseChange.isLocalization R S σ M).toIsLocalizationMap
  have ht := hcoef.mulEquiv_comp (Translations.DividedTranslations.algebraEquiv S σ I δ b hb)
  have he : (AffineMaps.DividedAffineMaps.map R S σ I δ b hb : GR → GS) =
      (Translations.DividedTranslations.algebraEquiv S σ I δ b hb) ∘ (AlgebraBaseChange.DividedAlgebraBaseChange.map R S σ) :=
    funext (fun t => DFunLike.congr_fun (map_factor R S σ I δ b hb IR δR hbase) t)
  rw [he]
  exact ht

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AffineLocalization.DividedAffineLocalization
