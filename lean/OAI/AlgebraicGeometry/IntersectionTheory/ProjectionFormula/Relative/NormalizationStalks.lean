import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationCharts
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Localization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizationDivisor

/-! # Normalization Stalks -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationStalks

noncomputable section

/-! Localizing relative normalization at a base point gives the integral
closure of its actual stalk in the extension field, with the entire fiber
and all local rings preserved. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.Normalization OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationCharts

universe u

variable (Y : Scheme.{u}) [IsIntegral Y] (L : Type u) [Field L] [Algebra Y.functionField L]

abbrev sectionAlgebra (U : Y.Opens) [Nonempty U] : Algebra Γ(Y, U) L :=
  ((algebraMap Y.functionField L).comp (algebraMap Γ(Y, U) Y.functionField)).toAlgebra

abbrev stalkAlgebra (y : Y) : Algebra (Y.presheaf.stalk y) L :=
  ((algebraMap Y.functionField L).comp (algebraMap (Y.presheaf.stalk y) Y.functionField)).toAlgebra

attribute [local instance] sectionAlgebra stalkAlgebra

instance sectionFieldTower (U : Y.Opens) [Nonempty U] :
    IsScalarTower Γ(Y, U) Y.functionField L := IsScalarTower.of_algebraMap_eq' rfl

instance stalkFieldTower (y : Y) : IsScalarTower (Y.presheaf.stalk y) Y.functionField L :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem sectionStalkTower (U : Y.Opens) [Nonempty U] (y : U) :
    letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf y
    IsScalarTower Γ(Y, U) (Y.presheaf.stalk y) L := by
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf y
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact congrArg (algebraMap Y.functionField L)
    (Scheme.algebraMap_germ_eq_germToFunctionField Y y.property a).symm

variable (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] (y : U)

local instance : Algebra Γ(Y, U) (Y.presheaf.stalk y) :=
  TopCat.Presheaf.algebra_section_stalk Y.presheaf y

local instance : IsScalarTower Γ(Y, U) (Y.presheaf.stalk y) L := sectionStalkTower Y L U y

def stalkInclusion : integralClosure Γ(Y, U) L →ₐ[Γ(Y, U)]
    integralClosure (Y.presheaf.stalk y) L := by
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf y
  let := sectionStalkTower Y L U y
  exact Normalization.Localization.closureInclusion Γ(Y, U) (Y.presheaf.stalk y) L

theorem stalk_isLocalization :
    letI := (stalkInclusion Y L U y).toRingHom.toAlgebra
    IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure Γ(Y, U) L)
        (hU.primeIdealOf y).asIdeal.primeCompl)
      (integralClosure (Y.presheaf.stalk y) L) := by
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf y
  let := sectionStalkTower Y L U y
  let := hU.isLocalization_stalk y
  exact Normalization.Localization.closure_isLocalization Γ(Y, U) (Y.presheaf.stalk y) L
    (hU.primeIdealOf y).asIdeal.primeCompl

def stalkMap : Spec (.of (integralClosure (Y.presheaf.stalk y) L)) ⟶ Normalization.relativeNormalization Y L :=
  Spec.map (CommRingCat.ofHom (stalkInclusion Y L U y).toRingHom) ≫ NormalizationCharts.chartMap Y L U hU

theorem stalkMap_comp : NormalizationStalks.stalkMap Y L U hU y ≫ Normalization.relativeNormalizationMap Y L =
    Spec.map (CommRingCat.ofHom
      (algebraMap (Y.presheaf.stalk y) (integralClosure (Y.presheaf.stalk y) L))) ≫
        Y.fromSpecStalk y := by
  rw [NormalizationStalks.stalkMap, Category.assoc, NormalizationCharts.chartMap_comp,
    ← hU.fromSpecStalk_eq_fromSpecStalk y.property, IsAffineOpen.fromSpecStalk,
    ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext a
  exact congrArg (algebraMap Y.functionField L)
    (Scheme.algebraMap_germ_eq_germToFunctionField Y y.property a).symm

theorem stalkMap_stalkMap_isIso (z : Spec (.of (integralClosure (Y.presheaf.stalk y) L))) :
    IsIso ((NormalizationStalks.stalkMap Y L U hU y).stalkMap z) := by
  let B := integralClosure Γ(Y, U) L
  let D := integralClosure (Y.presheaf.stalk y) L
  let := (stalkInclusion Y L U y).toRingHom.toAlgebra
  let M := Algebra.algebraMapSubmonoid B (hU.primeIdealOf y).asIdeal.primeCompl
  let : IsLocalization M D := stalk_isLocalization Y L U hU y
  let : IsIso ((Spec.map (CommRingCat.ofHom (algebraMap B D))).stalkMap z) :=
    LocalizationStalks.localization_stalkMap_isIso B D M z
  change IsIso ((Spec.map (CommRingCat.ofHom (algebraMap B D)) ≫ NormalizationCharts.chartMap Y L U hU).stalkMap z)
  rw [Scheme.Hom.stalkMap_comp]
  infer_instance

theorem stalkMap_residueDegree (z : Spec (.of (integralClosure (Y.presheaf.stalk y) L))) :
    (NormalizationStalks.stalkMap Y L U hU y).residueDegree z = 1 := by
  let := stalkMap_stalkMap_isIso Y L U hU y z
  exact Stalk.ResidueDegree.residueDegree_of_isIso_stalkMap _ _

theorem stalkMap_coheight (z : Spec (.of (integralClosure (Y.presheaf.stalk y) L))) :
    Order.coheight (NormalizationStalks.stalkMap Y L U hU y z) = Order.coheight z := by
  let B := integralClosure Γ(Y, U) L
  let D := integralClosure (Y.presheaf.stalk y) L
  let := (stalkInclusion Y L U y).toRingHom.toAlgebra
  let M := Algebra.algebraMapSubmonoid B (hU.primeIdealOf y).asIdeal.primeCompl
  let : IsLocalization M D := stalk_isLocalization Y L U hU y
  change Order.coheight (NormalizationCharts.chartMap Y L U hU
    ((Spec.map (CommRingCat.ofHom (algebraMap B D))) z)) = _
  rw [coheight_eq_of_isOpenImmersion]
  exact LocalizationStalks.localization_coheight B D M z

theorem stalkMap_genericPoint :
    NormalizationStalks.stalkMap Y L U hU y
      (genericPoint (Spec (.of (integralClosure (Y.presheaf.stalk y) L)))) =
        genericPoint (Normalization.relativeNormalization Y L) := by
  let B := integralClosure Γ(Y, U) L
  let D := integralClosure (Y.presheaf.stalk y) L
  let := (stalkInclusion Y L U y).toRingHom.toAlgebra
  let M := Algebra.algebraMapSubmonoid B (hU.primeIdealOf y).asIdeal.primeCompl
  let : IsLocalization M D := stalk_isLocalization Y L U hU y
  change NormalizationCharts.chartMap Y L U hU ((Spec.map (CommRingCat.ofHom (algebraMap B D)))
    (genericPoint (Spec (.of D)))) = _
  rw [LocalizationDivisor.localization_genericPoint B D M, genericPoint_eq_of_isOpenImmersion]

theorem stalkMap_injective : Function.Injective (NormalizationStalks.stalkMap Y L U hU y) := by
  let B := integralClosure Γ(Y, U) L
  let D := integralClosure (Y.presheaf.stalk y) L
  let := (stalkInclusion Y L U y).toRingHom.toAlgebra
  let M := Algebra.algebraMapSubmonoid B (hU.primeIdealOf y).asIdeal.primeCompl
  let : IsLocalization M D := stalk_isLocalization Y L U hU y
  exact (NormalizationCharts.chartMap Y L U hU).isOpenEmbedding.injective.comp
    (PrimeSpectrum.localization_comap_injective D M)

theorem stalkMap_covers_fiber (z : Normalization.relativeNormalization Y L)
    (hz : Normalization.relativeNormalizationMap Y L z = y) : z ∈ Set.range (NormalizationStalks.stalkMap Y L U hU y) := by
  let B := integralClosure Γ(Y, U) L
  let D := integralClosure (Y.presheaf.stalk y) L
  let := (stalkInclusion Y L U y).toRingHom.toAlgebra
  let M := Algebra.algebraMapSubmonoid B (hU.primeIdealOf y).asIdeal.primeCompl
  let : IsLocalization M D := stalk_isLocalization Y L U hU y
  have hzU : z ∈ Normalization.relativeNormalizationMap Y L ⁻¹ᵁ U := by
    change Normalization.relativeNormalizationMap Y L z ∈ U
    rw [hz]
    exact y.property
  change z ∈ (Normalization.relativeNormalizationMap Y L ⁻¹ᵁ U : Set (Normalization.relativeNormalization Y L)) at hzU
  rw [← NormalizationCharts.chartMap_range Y L U hU] at hzU
  obtain ⟨q, hq⟩ := hzU
  have hp : (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) B))) q = hU.primeIdealOf y := by
    apply hU.fromSpec.isOpenEmbedding.injective
    have hc := congrArg (fun i : Spec (.of B) ⟶ Y => i q) (NormalizationCharts.chartMap_comp Y L U hU)
    change Normalization.relativeNormalizationMap Y L (NormalizationCharts.chartMap Y L U hU q) =
      hU.fromSpec ((Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) B))) q) at hc
    rw [← hc, hq, hz, hU.fromSpec_primeIdealOf]
  have hdisj : Disjoint (M : Set B) (q.asIdeal : Set B) := by
    rw [Set.disjoint_left]
    intro z hzM hzq
    obtain ⟨a, ha, rfl⟩ := hzM
    apply ha
    have he := congrArg PrimeSpectrum.asIdeal hp
    change Ideal.comap (algebraMap Γ(Y, U) B) q.asIdeal = (hU.primeIdealOf y).asIdeal at he
    rw [← he]
    exact hzq
  have hqrange : q ∈ Set.range (PrimeSpectrum.comap (algebraMap B D)) := by
    rw [PrimeSpectrum.localization_comap_range D M]
    exact hdisj
  obtain ⟨w, hw⟩ := hqrange
  refine ⟨w, ?_⟩
  change NormalizationCharts.chartMap Y L U hU ((Spec.map (CommRingCat.ofHom (algebraMap B D))) w) = z
  exact (congrArg (NormalizationCharts.chartMap Y L U hU) hw).trans hq

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationStalks
