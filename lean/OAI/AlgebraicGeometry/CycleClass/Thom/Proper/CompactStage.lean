import OAI.AlgebraicGeometry.CycleClass.Thom.Proper.CompactSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSupportedCup

/-! # Compact Stage -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Proper.CompactStage.Constructions.HigherThom

noncomputable section

/-! The supported comparison at an ambient compact set is the exact source compact stage after taking the proper preimage. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def regularAmbientCompactThomStageIso (K : Compacts Z.regularAmbientSpace) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (CompactSupport.Constructions.HigherThom.regularCompactPreimage Z K : Set Z.regularAnalyticSpace)ᶜ q ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) (CompactSupport.Constructions.HigherThom.regularCompactPreimage Z K) : Set Z.regularAmbientSpace)ᶜ ((2 * p)+q) :=
  (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of Z.regularAnalyticSpace) S q) (CompactSupport.Constructions.HigherThom.regularCompactPreimage_sourceComplement Z K))).symm ≪≫
    GlobalSupportedSource.Constructions.HigherThom.regularSourceThomSupportedGlobalIso Z a ha (CompactSupport.Constructions.HigherThom.regularAmbientCompactComplement Z K) q ≪≫
    eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) S ((2 * p)+q)) (CompactSupport.Constructions.HigherThom.regularCompactPreimage_targetComplement Z K))

theorem regularAmbientCompactThomStageIso_eq_source (K : Compacts Z.regularAmbientSpace) (q : ℕ) :
    (regularAmbientCompactThomStageIso Z a ha K q).hom =
      (Regular.CompactStage.Constructions.HigherThom.regularSourceCompactThomStageIso Z a ha (CompactSupport.Constructions.HigherThom.regularCompactPreimage Z K) q).hom := by
  let h := CompactSupport.Constructions.HigherThom.regularAmbientCompactComplement_le_preimageImage Z K
  exact HodgeConjecture.DegreeTwo.LocalSupportNaturality.Constructions.relativeNormalizedSupportIso_eq (TopCat.of Z.regularAnalyticSpace) (TopCat.of Z.regularAmbientSpace) q ((2 * p)+q)
    (show ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj (CompactSupport.Constructions.HigherThom.regularAmbientCompactComplement Z K) : Set Z.regularAnalyticSpace) ⊆
      ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj (Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement Z (CompactSupport.Constructions.HigherThom.regularCompactPreimage Z K)) :
        Set Z.regularAnalyticSpace) from fun _ hx => h hx)
    (sup_le_sup_left h Z.regularThomComplementOpen)
    (GlobalSupportedSource.Constructions.HigherThom.regularSourceThomSupportedGlobalIso Z a ha (CompactSupport.Constructions.HigherThom.regularAmbientCompactComplement Z K) q)
    (GlobalSupportedSource.Constructions.HigherThom.regularSourceThomSupportedGlobalIso Z a ha (Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement Z (CompactSupport.Constructions.HigherThom.regularCompactPreimage Z K)) q)
    (CompactSupport.Constructions.HigherThom.regularCompactPreimage_sourceComplement Z K) (Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement_preimage Z (CompactSupport.Constructions.HigherThom.regularCompactPreimage Z K))
    (CompactSupport.Constructions.HigherThom.regularCompactPreimage_targetComplement Z K) (Regular.CompactStage.Constructions.HigherThom.regularCompactThom_unionComplement Z (CompactSupport.Constructions.HigherThom.regularCompactPreimage Z K))
    (GlobalSourceNaturality.Constructions.HigherThom.regularSourceThomSupportedGlobalIso_support_naturality Z a ha h q)

theorem regularAmbientCompactThomStageIso_cup (K : Compacts Z.regularAmbientSpace) (q : ℕ) :
    AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap K q ≫
      (regularAmbientCompactThomStageIso Z a ha K q).hom =
    ModuleCat.ofHom (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of Z.regularAmbientSpace)
      (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
      Z.regularThomComplementOpen.isOpen K.isCompact.isClosed.isOpen_compl (2 * p) q Z.regularThomClass) ≫
      (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of Z.regularAmbientSpace) S ((2 * p)+q)) (CompactSupport.Constructions.HigherThom.regularCompactPreimage_targetComplement Z K))).hom := by
  have hc := GlobalSupportedCup.Constructions.HigherThom.regularSourceThomSupportedGlobalIso_cup Z a ha (CompactSupport.Constructions.HigherThom.regularAmbientCompactComplement Z K) q
  change AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap K q ≫
      (GlobalSupportedSource.Constructions.HigherThom.regularSourceThomSupportedGlobalIso Z a ha (CompactSupport.Constructions.HigherThom.regularAmbientCompactComplement Z K) q).hom =
    ModuleCat.ofHom (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of Z.regularAmbientSpace)
      (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
      Z.regularThomComplementOpen.isOpen K.isCompact.isClosed.isOpen_compl (2 * p) q Z.regularThomClass) at hc
  let t := (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of Z.regularAmbientSpace) S ((2 * p)+q)) (CompactSupport.Constructions.HigherThom.regularCompactPreimage_targetComplement Z K))).hom
  have hs : (regularAmbientCompactThomStageIso Z a ha K q).hom =
      (GlobalSupportedSource.Constructions.HigherThom.regularSourceThomSupportedGlobalIso Z a ha (CompactSupport.Constructions.HigherThom.regularAmbientCompactComplement Z K) q).hom ≫ t := by
    change 𝟙 _ ≫ ((GlobalSupportedSource.Constructions.HigherThom.regularSourceThomSupportedGlobalIso Z a ha (CompactSupport.Constructions.HigherThom.regularAmbientCompactComplement Z K) q).hom ≫ t) =
      (GlobalSupportedSource.Constructions.HigherThom.regularSourceThomSupportedGlobalIso Z a ha (CompactSupport.Constructions.HigherThom.regularAmbientCompactComplement Z K) q).hom ≫ t
    exact Category.id_comp _
  rw [hs, ← Category.assoc, hc]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Proper.CompactStage.Constructions.HigherThom
