import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage

/-! # Base Image Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.BaseImageRestriction.Constructions.Class

noncomputable section

/-! The parent cycle class in its image support is the direct ambient
pullback, and its classes on nested analytic opens restrict literally. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.Class

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Opens V.analyticSpace)

 theorem baseImageComplement_mapsTo :
    Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
      (Set.range (Normalization.BaseImage.Constructions.Class.baseImage D U))ᶜ (Set.range D.analyticInclusion)ᶜ :=
  fun x hx hy => hx ⟨⟨x, hy⟩, rfl⟩

 theorem baseImageCycleClass_eq_direct : Normalization.BaseImage.Constructions.Class.baseImageCycleClass D U =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
      (baseImageComplement_mapsTo D U) (2 * p) D.rationalSupportedCycleClass := by
  let hcast : Set.MapsTo (𝟙 (TopCat.of U)) (Set.range (Normalization.BaseImage.Constructions.Class.baseImage D U))ᶜ (NormalizationAffine.SectionSupport.Constructions.parentBaseSupport D U)ᶜ :=
    fun x hx hy => hx ⟨⟨x, hy⟩, rfl⟩
  have he : Normalization.BaseImage.Constructions.Class.baseImageCycleClass D U =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U)) hcast (2 * p)
        (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
          (Set.range D.analyticInclusion)ᶜ U (2 * p) D.rationalSupportedCycleClass) := by
    change eqToHom (congrArg
      (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) A (2 * p))
      (congrArg Set.compl (Normalization.BaseImage.Constructions.Class.baseImage_range D U).symm)) _ = _
    exact (ConcreteCategory.congr_hom
      (Supported.Transport.Constructions.Class.identityMap_eq_supportCast (TopCat.of U) (congrArg Set.compl (Normalization.BaseImage.Constructions.Class.baseImage_range D U).symm) hcast (2 * p)) _).symm
  exact he.trans (ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace)) hcast (fun _ hx => hx) (2 * p))
    D.rationalSupportedCycleClass)

variable (P : Opens V.analyticSpace) (hPU : P ≤ U)

 theorem baseImage_restriction_mapsTo :
    Set.MapsTo ((Opens.toTopCat (TopCat.of V.analyticSpace)).map (homOfLE hPU))
      (Set.range (Normalization.BaseImage.Constructions.Class.baseImage D P))ᶜ (Set.range (Normalization.BaseImage.Constructions.Class.baseImage D U))ᶜ := by
  intro x hx hy
  apply hx
  rw [Normalization.BaseImage.Constructions.Class.baseImage_range] at hy ⊢
  exact hy

 theorem baseImageCycleClass_restrict :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      ((Opens.toTopCat (TopCat.of V.analyticSpace)).map (homOfLE hPU))
      (baseImage_restriction_mapsTo D U P hPU) (2 * p) (Normalization.BaseImage.Constructions.Class.baseImageCycleClass D U) = Normalization.BaseImage.Constructions.Class.baseImageCycleClass D P := by
  rw [baseImageCycleClass_eq_direct, baseImageCycleClass_eq_direct]
  exact ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    ((Opens.toTopCat (TopCat.of V.analyticSpace)).map (homOfLE hPU))
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
    (baseImage_restriction_mapsTo D U P hPU) (baseImageComplement_mapsTo D U) (2 * p))
    D.rationalSupportedCycleClass

end

end OAI.AlgebraicGeometry.CycleClass.Thom.BaseImageRestriction.Constructions.Class
