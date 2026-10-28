import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.ProperCompactSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSupportedCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNaturality

/-! # Compact Proper Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.CompactProperCup.Constructions.Construction

noncomputable section

section

/-! The supported comparison at an ambient compact set is the exact source compact stage after taking the proper preimage. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNaturality.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def regularAmbientCompactThomStageIso (K : Compacts Z.regularAmbientSpace) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (ProperCompactSupport.Constructions.Construction.regularCompactPreimage Z K : Set Z.regularAnalyticSpace)ᶜ q ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) (ProperCompactSupport.Constructions.Construction.regularCompactPreimage Z K) : Set Z.regularAmbientSpace)ᶜ ((2 * p)+q) :=
  (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of Z.regularAnalyticSpace) S q) (ProperCompactSupport.Constructions.Construction.regularCompactPreimage_sourceComplement Z K))).symm ≪≫
    SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha (ProperCompactSupport.Constructions.Construction.regularAmbientCompactComplement Z K) q ≪≫
    eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) S ((2 * p)+q)) (ProperCompactSupport.Constructions.Construction.regularCompactPreimage_targetComplement Z K))

theorem regularAmbientCompactThomStageIso_eq_source (K : Compacts Z.regularAmbientSpace) (q : ℕ) :
    (regularAmbientCompactThomStageIso Z a ha K q).hom =
      (SupportedThomSource.Constructions.Construction.regularSourceCompactThomStageIso Z a ha (ProperCompactSupport.Constructions.Construction.regularCompactPreimage Z K) q).hom := by
  let h := ProperCompactSupport.Constructions.Construction.regularAmbientCompactComplement_le_preimageImage Z K
  exact HodgeConjecture.DegreeTwo.LocalSupportNaturality.Constructions.relativeNormalizedSupportIso_eq (TopCat.of Z.regularAnalyticSpace) (TopCat.of Z.regularAmbientSpace) q ((2 * p)+q)
    (show ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj (ProperCompactSupport.Constructions.Construction.regularAmbientCompactComplement Z K) : Set Z.regularAnalyticSpace) ⊆
      ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj (SupportedThomSource.Constructions.Construction.regularCompactImageComplement Z (ProperCompactSupport.Constructions.Construction.regularCompactPreimage Z K)) :
        Set Z.regularAnalyticSpace) from fun _ hx => h hx)
    (sup_le_sup_left h Z.regularThomComplementOpen)
    (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha (ProperCompactSupport.Constructions.Construction.regularAmbientCompactComplement Z K) q)
    (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha (SupportedThomSource.Constructions.Construction.regularCompactImageComplement Z (ProperCompactSupport.Constructions.Construction.regularCompactPreimage Z K)) q)
    (ProperCompactSupport.Constructions.Construction.regularCompactPreimage_sourceComplement Z K) (SupportedThomSource.Constructions.Construction.regularCompactImageComplement_preimage Z (ProperCompactSupport.Constructions.Construction.regularCompactPreimage Z K))
    (ProperCompactSupport.Constructions.Construction.regularCompactPreimage_targetComplement Z K) (SupportedThomSource.Constructions.Construction.regularCompactThom_unionComplement Z (ProperCompactSupport.Constructions.Construction.regularCompactPreimage Z K))
    (GlobalSourceNaturality.Constructions.Construction.regularSourceThomSupportedGlobalIso_support_naturality Z a ha h q)

theorem regularAmbientCompactThomStageIso_cup (K : Compacts Z.regularAmbientSpace) (q : ℕ) :
    AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap K q ≫
      (regularAmbientCompactThomStageIso Z a ha K q).hom =
    ModuleCat.ofHom (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of Z.regularAmbientSpace)
      (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
      Z.regularThomComplementOpen.isOpen K.isCompact.isClosed.isOpen_compl (2 * p) q Z.regularThomClass) ≫
      (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of Z.regularAmbientSpace) S ((2 * p)+q)) (ProperCompactSupport.Constructions.Construction.regularCompactPreimage_targetComplement Z K))).hom := by
  have hc := GlobalSupportedCup.Constructions.Construction.regularSourceThomSupportedGlobalIso_cup Z a ha (ProperCompactSupport.Constructions.Construction.regularAmbientCompactComplement Z K) q
  change AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap K q ≫
      (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha (ProperCompactSupport.Constructions.Construction.regularAmbientCompactComplement Z K) q).hom =
    ModuleCat.ofHom (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of Z.regularAmbientSpace)
      (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
      Z.regularThomComplementOpen.isOpen K.isCompact.isClosed.isOpen_compl (2 * p) q Z.regularThomClass) at hc
  let t := (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of Z.regularAmbientSpace) S ((2 * p)+q)) (ProperCompactSupport.Constructions.Construction.regularCompactPreimage_targetComplement Z K))).hom
  have hs : (regularAmbientCompactThomStageIso Z a ha K q).hom =
      (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha (ProperCompactSupport.Constructions.Construction.regularAmbientCompactComplement Z K) q).hom ≫ t := by
    change 𝟙 _ ≫ ((SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha (ProperCompactSupport.Constructions.Construction.regularAmbientCompactComplement Z K) q).hom ≫ t) =
      (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha (ProperCompactSupport.Constructions.Construction.regularAmbientCompactComplement Z K) q).hom ≫ t
    exact Category.id_comp _
  rw [hs, ← Category.assoc, hc]

end

/-! Proper pullback followed by the global compact Thom pushforward is actual left cup by the underlying regular Thom class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNaturality.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceCompactThomPushforward_properPullback (q : ℕ) :
    AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap q ≫
      SourceCompactPushforward.Constructions.Construction.regularSourceCompactThomPushforward Z a ha q =
    HodgeConjecture.DegreeTwo.CompactLeftCup.Constructions.compactCohomologyLeftCup (TopCat.of Z.regularAmbientSpace) (2 * p) q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
        (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) (2 * p) Z.regularThomClass) := by
  apply AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_hom_ext (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) q
  intro K
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  let J := ProperCompactSupport.Constructions.Construction.regularCompactPreimage Z K
  let I := HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) J
  let C := (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)
  let v := HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of Z.regularAmbientSpace) C (K : Set Z.regularAmbientSpace)ᶜ
    Z.regularThomComplementOpen.isOpen K.isCompact.isClosed.isOpen_compl (2 * p) q Z.regularThomClass b
  have hp := ConcreteCategory.congr_hom (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportCohomologyι_properPullback (ModuleCat.of ℚ ℚ)
    Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap K q) b
  have hs := ConcreteCategory.congr_hom (SourceCompactPushforward.Constructions.Construction.regularSourceCompactThomPushforward_stage Z a ha q J)
    (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap K q b)
  rw [← regularAmbientCompactThomStageIso_eq_source Z a ha K q] at hs
  have hc := ConcreteCategory.congr_hom (regularAmbientCompactThomStageIso_cup Z a ha K q) b
  have he := HodgeConjecture.DegreeTwo.CompactPointNaturality.Constructions.compactSupportCohomologyι_supportCast (TopCat.of Z.regularAmbientSpace) I
    (HodgeConjecture.DegreeTwo.CompactThomCupSupport.Constructions.thomCompactIntersection (TopCat.of Z.regularAmbientSpace) C Z.regularThomComplementOpen.isOpen K)
    (ProperCompactSupport.Constructions.Construction.regularCompactPreimage_image Z K) (C ∪ (K : Set Z.regularAmbientSpace)ᶜ)
    (ProperCompactSupport.Constructions.Construction.regularCompactPreimage_targetComplement Z K)
    (HodgeConjecture.DegreeTwo.CompactThomCupSupport.Constructions.thomCompactIntersection_complement (TopCat.of Z.regularAmbientSpace) C Z.regularThomComplementOpen.isOpen K)
    ((2 * p)+q) v
  have ht := HodgeConjecture.DegreeTwo.CompactThomCupSupport.Constructions.compactThomCup_retains_intersection (TopCat.of Z.regularAmbientSpace) C
    Z.regularThomComplementOpen.isOpen (2 * p) q Z.regularThomClass K b
  exact ((congrArg (SourceCompactPushforward.Constructions.Construction.regularSourceCompactThomPushforward Z a ha q) hp).trans hs).trans
    ((congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) I ((2 * p)+q)) hc).trans
      (he.trans ht.symm))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.CompactProperCup.Constructions.Construction
