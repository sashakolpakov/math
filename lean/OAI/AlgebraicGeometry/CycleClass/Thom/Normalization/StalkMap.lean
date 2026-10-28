import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Charts
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ClosureLocalization
import OAI.AlgebraicGeometry.CycleClass.Thom.LocalizationRationalOrder

/-! # Stalk Map -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.StalkMap.Constructions.Local

noncomputable section

/-!
# ThomClass: normalized local rings inside the actual global normalization

The spectrum of the integral closure of a stalk maps into the global
normalization through an actual integral-closure chart. It lies over the
original stalk map, preserves local rings and codimensions, and induces
the actual generic-field comparison.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Charts.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ClosureLocalization.Constructions
  LocalizationStalks.Constructions LocalizationRationalOrder.Constructions

universe u
variable (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (x : U)

def normalizationStalkMap :
    Spec (CommRingCat.of (integralClosure (X.presheaf.stalk x) X.functionField)) ⟶ Normalization.Scheme.Constructions.normalization X :=
  Spec.map (CommRingCat.ofHom (Integral.ClosureLocalization.Constructions.normalizationStalkInclusion X U x).toRingHom) ≫ Charts.Constructions.normalizationChartMap X U hU

theorem normalizationStalkMap_comp :
    normalizationStalkMap X U hU x ≫ Normalization.Scheme.Constructions.normalizationMap X =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
        (integralClosure (X.presheaf.stalk x) X.functionField))) ≫ X.fromSpecStalk x := by
  rw [normalizationStalkMap, Category.assoc, Charts.Constructions.normalizationChartMap_comp,
    ← hU.fromSpecStalk_eq_fromSpecStalk x.property, IsAffineOpen.fromSpecStalk,
    ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext a
  exact (Scheme.algebraMap_germ_eq_germToFunctionField X x.property a).symm

theorem normalizationStalkMap_stalkMap_isIso
    (y : Spec (CommRingCat.of (integralClosure (X.presheaf.stalk x) X.functionField))) :
    IsIso ((normalizationStalkMap X U hU x).stalkMap y) := by
  let B := integralClosure Γ(X, U) X.functionField
  let D := integralClosure (X.presheaf.stalk x) X.functionField
  let := (Integral.ClosureLocalization.Constructions.normalizationStalkInclusion X U x).toRingHom.toAlgebra
  let M := Algebra.algebraMapSubmonoid B (hU.primeIdealOf x).asIdeal.primeCompl
  let : IsLocalization M D := Integral.ClosureLocalization.Constructions.normalizationStalk_isLocalization X U hU x
  let l := Spec.map (CommRingCat.ofHom (algebraMap B D))
  let c := Charts.Constructions.normalizationChartMap X U hU
  have hl : IsIso (l.stalkMap y) := LocalizationStalks.Constructions.localizationStalkMap_isIso B D M y
  have hc : IsIso (c.stalkMap (l y)) := inferInstance
  let e := (@asIso _ _ _ _ (c.stalkMap (l y)) hc) ≪≫ (@asIso _ _ _ _ (l.stalkMap y) hl)
  have he : e.hom = (l ≫ c).stalkMap y := (Scheme.Hom.stalkMap_comp l c y).symm
  exact (congrArg (fun k => IsIso k) he).mp e.isIso_hom

theorem normalizationStalkMap_coheight
    (y : Spec (CommRingCat.of (integralClosure (X.presheaf.stalk x) X.functionField))) :
    Order.coheight (normalizationStalkMap X U hU x y) = Order.coheight y := by
  let B := integralClosure Γ(X, U) X.functionField
  let D := integralClosure (X.presheaf.stalk x) X.functionField
  let := (Integral.ClosureLocalization.Constructions.normalizationStalkInclusion X U x).toRingHom.toAlgebra
  let M := Algebra.algebraMapSubmonoid B (hU.primeIdealOf x).asIdeal.primeCompl
  let : IsLocalization M D := Integral.ClosureLocalization.Constructions.normalizationStalk_isLocalization X U hU x
  change Order.coheight (Charts.Constructions.normalizationChartMap X U hU ((Spec.map (CommRingCat.ofHom (algebraMap B D))) y)) = _
  rw [coheight_eq_of_isOpenImmersion]
  exact LocalizationStalks.Constructions.localization_coheight B D M y

theorem normalizationStalkMap_genericPoint :
    normalizationStalkMap X U hU x
      (genericPoint (Spec (CommRingCat.of (integralClosure (X.presheaf.stalk x) X.functionField)))) =
      genericPoint (Normalization.Scheme.Constructions.normalization X) := by
  let B := integralClosure Γ(X, U) X.functionField
  let D := integralClosure (X.presheaf.stalk x) X.functionField
  let := (Integral.ClosureLocalization.Constructions.normalizationStalkInclusion X U x).toRingHom.toAlgebra
  let M := Algebra.algebraMapSubmonoid B (hU.primeIdealOf x).asIdeal.primeCompl
  let : IsLocalization M D := Integral.ClosureLocalization.Constructions.normalizationStalk_isLocalization X U hU x
  change Charts.Constructions.normalizationChartMap X U hU
    ((Spec.map (CommRingCat.ofHom (algebraMap B D))) (genericPoint (Spec (CommRingCat.of D)))) = _
  rw [LocalizationRationalOrder.Constructions.localization_genericPoint B D M, genericPoint_eq_of_isOpenImmersion]

theorem normalizationStalkMap_injective : Function.Injective (normalizationStalkMap X U hU x) := by
  let B := integralClosure Γ(X, U) X.functionField
  let D := integralClosure (X.presheaf.stalk x) X.functionField
  let := (Integral.ClosureLocalization.Constructions.normalizationStalkInclusion X U x).toRingHom.toAlgebra
  let M := Algebra.algebraMapSubmonoid B (hU.primeIdealOf x).asIdeal.primeCompl
  let : IsLocalization M D := Integral.ClosureLocalization.Constructions.normalizationStalk_isLocalization X U hU x
  exact (Charts.Constructions.normalizationChartMap X U hU).isOpenEmbedding.injective.comp
    (PrimeSpectrum.localization_comap_injective D M)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.StalkMap.Constructions.Local
