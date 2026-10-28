import OAI.AlgebraicGeometry.CycleClass.Thom.BaseImageRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift

/-! # Base Image Enlargement -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.BaseImageEnlargement.Constructions.Class

noncomputable section

/-! Enlarging the original parent-cycle image support gives precisely
the canonical supported-cycle generator in the common analytic support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.BaseImageRestriction.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (U : Opens V.analyticSpace) {L : Type} (u : L → U)
  (hD : (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ Set.range u)

include hD in
theorem parentImage_mapsTo : Set.MapsTo (𝟙 (TopCat.of U)) (Set.range u)ᶜ (Set.range (Normalization.BaseImage.Constructions.Class.baseImage D U))ᶜ := by
  intro x hx hy
  apply hx
  rw [Normalization.BaseImage.Constructions.Class.baseImage_range] at hy
  exact hD hy

theorem parentClass_enlarge_eq_generator :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (parentImage_mapsTo D U u hD) (2 * p) (Normalization.BaseImage.Constructions.Class.baseImageCycleClass D U) =
    Open.SupportedLift.Constructions.Map.relativeGenerator V U (Set.range u) p ⟨D, hD⟩ := by
  rw [BaseImageRestriction.Constructions.Class.baseImageCycleClass_eq_direct]
  exact ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of U)) (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
    (parentImage_mapsTo D U u hD) (BaseImageRestriction.Constructions.Class.baseImageComplement_mapsTo D U) (2 * p)) D.rationalSupportedCycleClass

end

end OAI.AlgebraicGeometry.CycleClass.Thom.BaseImageEnlargement.Constructions.Class
