import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Localization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizationDivisor

/-! # Stalk Map -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.StalkMap

noncomputable section

/-! The spectrum of a normalized stalk maps canonically into the global
normalization. Its stalk maps are isomorphisms, and it preserves native
residue degrees and codimensions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Charts OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Localization

universe u

variable (X : Scheme.{u}) [IsIntegral X]
  (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (x : U)

def normalizationStalkMap :
    Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField)) ⟶ Normalization.Scheme.normalization X :=
  Spec.map (CommRingCat.ofHom (Localization.normalizationStalkInclusion X U x).toRingHom) ≫
    Charts.normalizationChartMap X U hU

theorem normalizationStalkMap_comp :
    normalizationStalkMap X U hU x ≫ Normalization.Scheme.normalizationMap X =
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x)
          (integralClosure (X.presheaf.stalk x) X.functionField))) ≫ X.fromSpecStalk x := by
  rw [normalizationStalkMap, Category.assoc, Charts.normalizationChartMap_comp,
    ← hU.fromSpecStalk_eq_fromSpecStalk x.property, IsAffineOpen.fromSpecStalk,
    ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext a
  exact (Scheme.algebraMap_germ_eq_germToFunctionField X x.property a).symm

theorem normalizationStalkMap_stalkMap_isIso
    (y : Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField))) :
    IsIso ((normalizationStalkMap X U hU x).stalkMap y) := by
  let B := integralClosure Γ(X, U) X.functionField
  let D := integralClosure (X.presheaf.stalk x) X.functionField
  let := (Localization.normalizationStalkInclusion X U x).toRingHom.toAlgebra
  let M := Algebra.algebraMapSubmonoid B (hU.primeIdealOf x).asIdeal.primeCompl
  let : IsLocalization M D := Localization.normalizationStalk_isLocalization X U hU x
  let : IsIso ((Spec.map (CommRingCat.ofHom (algebraMap B D))).stalkMap y) :=
    LocalizationStalks.localization_stalkMap_isIso B D M y
  change IsIso ((Spec.map (CommRingCat.ofHom (algebraMap B D)) ≫
    Charts.normalizationChartMap X U hU).stalkMap y)
  rw [Scheme.Hom.stalkMap_comp]
  infer_instance

theorem normalizationStalkMap_residueDegree
    (y : Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField))) :
    (normalizationStalkMap X U hU x).residueDegree y = 1 := by
  let := normalizationStalkMap_stalkMap_isIso X U hU x y
  exact Stalk.ResidueDegree.residueDegree_of_isIso_stalkMap _ _

theorem normalizationStalkMap_coheight
    (y : Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField))) :
    Order.coheight (normalizationStalkMap X U hU x y) = Order.coheight y := by
  let B := integralClosure Γ(X, U) X.functionField
  let D := integralClosure (X.presheaf.stalk x) X.functionField
  let := (Localization.normalizationStalkInclusion X U x).toRingHom.toAlgebra
  let M := Algebra.algebraMapSubmonoid B (hU.primeIdealOf x).asIdeal.primeCompl
  let : IsLocalization M D := Localization.normalizationStalk_isLocalization X U hU x
  change Order.coheight (Charts.normalizationChartMap X U hU
    ((Spec.map (CommRingCat.ofHom (algebraMap B D))) y)) = _
  rw [coheight_eq_of_isOpenImmersion]
  exact LocalizationStalks.localization_coheight B D M y

theorem normalizationStalkMap_genericPoint :
    normalizationStalkMap X U hU x
      (genericPoint (Spec (.of (integralClosure (X.presheaf.stalk x) X.functionField)))) =
        genericPoint (Normalization.Scheme.normalization X) := by
  let B := integralClosure Γ(X, U) X.functionField
  let D := integralClosure (X.presheaf.stalk x) X.functionField
  let := (Localization.normalizationStalkInclusion X U x).toRingHom.toAlgebra
  let M := Algebra.algebraMapSubmonoid B (hU.primeIdealOf x).asIdeal.primeCompl
  let : IsLocalization M D := Localization.normalizationStalk_isLocalization X U hU x
  change Charts.normalizationChartMap X U hU
    ((Spec.map (CommRingCat.ofHom (algebraMap B D))) (genericPoint (Spec (.of D)))) = _
  rw [LocalizationDivisor.localization_genericPoint B D M,
    genericPoint_eq_of_isOpenImmersion]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.StalkMap
