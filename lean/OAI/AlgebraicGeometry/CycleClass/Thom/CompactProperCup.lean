import OAI.AlgebraicGeometry.CycleClass.Thom.Proper.CompactStage
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNaturality

/-! # Compact Proper Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.CompactProperCup.Constructions.HigherThom

noncomputable section

/-! Proper pullback followed by the global compact Thom pushforward is actual left cup by the underlying regular Thom class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNaturality.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceCompactThomPushforward_properPullback (q : ℕ) :
    AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap q ≫
      SourceCompactPushforward.Constructions.HigherThom.regularSourceCompactThomPushforward Z a ha q =
    HodgeConjecture.DegreeTwo.CompactLeftCup.Constructions.compactCohomologyLeftCup (TopCat.of Z.regularAmbientSpace) (2 * p) q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
        (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) (2 * p) Z.regularThomClass) := by
  apply AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_hom_ext (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) q
  intro K
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  let J := Proper.CompactSupport.Constructions.HigherThom.regularCompactPreimage Z K
  let I := HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) J
  let C := (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)
  let v := HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of Z.regularAmbientSpace) C (K : Set Z.regularAmbientSpace)ᶜ
    Z.regularThomComplementOpen.isOpen K.isCompact.isClosed.isOpen_compl (2 * p) q Z.regularThomClass b
  have hp := ConcreteCategory.congr_hom (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportCohomologyι_properPullback (ModuleCat.of ℚ ℚ)
    Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap K q) b
  have hs := ConcreteCategory.congr_hom (SourceCompactPushforward.Constructions.HigherThom.regularSourceCompactThomPushforward_stage Z a ha q J)
    (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap K q b)
  rw [← Proper.CompactStage.Constructions.HigherThom.regularAmbientCompactThomStageIso_eq_source Z a ha K q] at hs
  have hc := ConcreteCategory.congr_hom (Proper.CompactStage.Constructions.HigherThom.regularAmbientCompactThomStageIso_cup Z a ha K q) b
  have he := HodgeConjecture.DegreeTwo.CompactPointNaturality.Constructions.compactSupportCohomologyι_supportCast (TopCat.of Z.regularAmbientSpace) I
    (HodgeConjecture.DegreeTwo.CompactThomCupSupport.Constructions.thomCompactIntersection (TopCat.of Z.regularAmbientSpace) C Z.regularThomComplementOpen.isOpen K)
    (Proper.CompactSupport.Constructions.HigherThom.regularCompactPreimage_image Z K) (C ∪ (K : Set Z.regularAmbientSpace)ᶜ)
    (Proper.CompactSupport.Constructions.HigherThom.regularCompactPreimage_targetComplement Z K)
    (HodgeConjecture.DegreeTwo.CompactThomCupSupport.Constructions.thomCompactIntersection_complement (TopCat.of Z.regularAmbientSpace) C Z.regularThomComplementOpen.isOpen K)
    ((2 * p)+q) v
  have ht := HodgeConjecture.DegreeTwo.CompactThomCupSupport.Constructions.compactThomCup_retains_intersection (TopCat.of Z.regularAmbientSpace) C
    Z.regularThomComplementOpen.isOpen (2 * p) q Z.regularThomClass K b
  exact ((congrArg (SourceCompactPushforward.Constructions.HigherThom.regularSourceCompactThomPushforward Z a ha q) hp).trans hs).trans
    ((congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) I ((2 * p)+q)) hc).trans
      (he.trans ht.symm))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.CompactProperCup.Constructions.HigherThom
