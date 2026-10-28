import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ProperCompactThomSupport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GlobalSupportedThomCup

/-! # Proper Compact Thom Stage -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ProperCompactThomStage.Constructions

noncomputable section

/-! The supported comparison at an ambient compact set is the exact source compact stage after taking the proper preimage. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

def regularAmbientCompactThomStageIso (K : Compacts Z.regularAmbientSpace) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (ProperCompactThomSupport.Constructions.regularCompactPreimage Z K : Set Z.regularAnalyticSpace)ᶜ q ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) (ProperCompactThomSupport.Constructions.regularCompactPreimage Z K) : Set Z.regularAmbientSpace)ᶜ (2+q) :=
  (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of Z.regularAnalyticSpace) S q) (ProperCompactThomSupport.Constructions.regularCompactPreimage_sourceComplement Z K))).symm ≪≫
    GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso Z a ha (ProperCompactThomSupport.Constructions.regularAmbientCompactComplement Z K) q ≪≫
    eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) S (2+q)) (ProperCompactThomSupport.Constructions.regularCompactPreimage_targetComplement Z K))

theorem regularAmbientCompactThomStageIso_eq_source (K : Compacts Z.regularAmbientSpace) (q : ℕ) :
    (regularAmbientCompactThomStageIso Z a ha K q).hom =
      (RegularCompactThomStage.Constructions.regularSourceCompactThomStageIso Z a ha (ProperCompactThomSupport.Constructions.regularCompactPreimage Z K) q).hom := by
  let h := ProperCompactThomSupport.Constructions.regularAmbientCompactComplement_le_preimageImage Z K
  exact LocalSupportNaturality.Constructions.relativeNormalizedSupportIso_eq (TopCat.of Z.regularAnalyticSpace) (TopCat.of Z.regularAmbientSpace) q (2+q)
    (show ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj (ProperCompactThomSupport.Constructions.regularAmbientCompactComplement Z K) : Set Z.regularAnalyticSpace) ⊆
      ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj (RegularCompactThomStage.Constructions.regularCompactImageComplement Z (ProperCompactThomSupport.Constructions.regularCompactPreimage Z K)) :
        Set Z.regularAnalyticSpace) from fun _ hx => h hx)
    (sup_le_sup_left h Z.regularThomComplementOpen)
    (GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso Z a ha (ProperCompactThomSupport.Constructions.regularAmbientCompactComplement Z K) q)
    (GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso Z a ha (RegularCompactThomStage.Constructions.regularCompactImageComplement Z (ProperCompactThomSupport.Constructions.regularCompactPreimage Z K)) q)
    (ProperCompactThomSupport.Constructions.regularCompactPreimage_sourceComplement Z K) (RegularCompactThomStage.Constructions.regularCompactImageComplement_preimage Z (ProperCompactThomSupport.Constructions.regularCompactPreimage Z K))
    (ProperCompactThomSupport.Constructions.regularCompactPreimage_targetComplement Z K) (RegularCompactThomStage.Constructions.regularCompactThom_unionComplement Z (ProperCompactThomSupport.Constructions.regularCompactPreimage Z K))
    (GlobalSourceThomNaturality.Constructions.regularSourceThomSupportedGlobalIso_support_naturality Z a ha h q)

theorem regularAmbientCompactThomStageIso_cup (K : Compacts Z.regularAmbientSpace) (q : ℕ) :
    AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap K q ≫
      (regularAmbientCompactThomStageIso Z a ha K q).hom =
    ModuleCat.ofHom (SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of Z.regularAmbientSpace)
      (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
      Z.regularThomComplementOpen.isOpen K.isCompact.isClosed.isOpen_compl 2 q Z.regularThomClass) ≫
      (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of Z.regularAmbientSpace) S (2+q)) (ProperCompactThomSupport.Constructions.regularCompactPreimage_targetComplement Z K))).hom := by
  have hc := GlobalSupportedThomCup.Constructions.regularSourceThomSupportedGlobalIso_cup Z a ha (ProperCompactThomSupport.Constructions.regularAmbientCompactComplement Z K) q
  change AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap K q ≫
      (GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso Z a ha (ProperCompactThomSupport.Constructions.regularAmbientCompactComplement Z K) q).hom =
    ModuleCat.ofHom (SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of Z.regularAmbientSpace)
      (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
      Z.regularThomComplementOpen.isOpen K.isCompact.isClosed.isOpen_compl 2 q Z.regularThomClass) at hc
  let t := (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of Z.regularAmbientSpace) S (2+q)) (ProperCompactThomSupport.Constructions.regularCompactPreimage_targetComplement Z K))).hom
  have hs : (regularAmbientCompactThomStageIso Z a ha K q).hom =
      (GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso Z a ha (ProperCompactThomSupport.Constructions.regularAmbientCompactComplement Z K) q).hom ≫ t := by
    change 𝟙 _ ≫ ((GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso Z a ha (ProperCompactThomSupport.Constructions.regularAmbientCompactComplement Z K) q).hom ≫ t) =
      (GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso Z a ha (ProperCompactThomSupport.Constructions.regularAmbientCompactComplement Z K) q).hom ≫ t
    exact Category.id_comp _
  rw [hs, ← Category.assoc, hc]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ProperCompactThomStage.Constructions
