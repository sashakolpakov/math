import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ProperCompactThomStage
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNaturality

/-! # Compact Thom Proper Cup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomProperCup.Constructions

noncomputable section

/-! Proper pullback followed by the global compact Thom pushforward is actual left cup by the underlying regular Thom class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceCompactThomPushforward_properPullback (q : ℕ) :
    AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap q ≫
      CompactThomZero.Constructions.regularSourceCompactThomPushforward Z a ha q =
    CompactLeftCup.Constructions.compactCohomologyLeftCup (TopCat.of Z.regularAmbientSpace) 2 q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
        (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) 2 Z.regularThomClass) := by
  apply AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_hom_ext (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) q
  intro K
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  let J := ProperCompactThomSupport.Constructions.regularCompactPreimage Z K
  let I := OpenEmbeddingExtension.Constructions.embeddingCompactImage (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) J
  let C := (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)
  let v := SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of Z.regularAmbientSpace) C (K : Set Z.regularAmbientSpace)ᶜ
    Z.regularThomComplementOpen.isOpen K.isCompact.isClosed.isOpen_compl 2 q Z.regularThomClass b
  have hp := ConcreteCategory.congr_hom (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportCohomologyι_properPullback (ModuleCat.of ℚ ℚ)
    Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap K q) b
  have hs := ConcreteCategory.congr_hom (CompactThomZero.Constructions.regularSourceCompactThomPushforward_stage Z a ha q J)
    (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap K q b)
  rw [← ProperCompactThomStage.Constructions.regularAmbientCompactThomStageIso_eq_source Z a ha K q] at hs
  have hc := ConcreteCategory.congr_hom (ProperCompactThomStage.Constructions.regularAmbientCompactThomStageIso_cup Z a ha K q) b
  have he := CompactPointNaturality.Constructions.compactSupportCohomologyι_supportCast (TopCat.of Z.regularAmbientSpace) I
    (CompactThomCupSupport.Constructions.thomCompactIntersection (TopCat.of Z.regularAmbientSpace) C Z.regularThomComplementOpen.isOpen K)
    (ProperCompactThomSupport.Constructions.regularCompactPreimage_image Z K) (C ∪ (K : Set Z.regularAmbientSpace)ᶜ)
    (ProperCompactThomSupport.Constructions.regularCompactPreimage_targetComplement Z K)
    (CompactThomCupSupport.Constructions.thomCompactIntersection_complement (TopCat.of Z.regularAmbientSpace) C Z.regularThomComplementOpen.isOpen K)
    (2+q) v
  have ht := CompactThomCupSupport.Constructions.compactThomCup_retains_intersection (TopCat.of Z.regularAmbientSpace) C
    Z.regularThomComplementOpen.isOpen 2 q Z.regularThomClass K b
  exact ((congrArg (CompactThomZero.Constructions.regularSourceCompactThomPushforward Z a ha q) hp).trans hs).trans
    ((congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) I (2+q)) hc).trans
      (he.trans ht.symm))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomProperCup.Constructions
