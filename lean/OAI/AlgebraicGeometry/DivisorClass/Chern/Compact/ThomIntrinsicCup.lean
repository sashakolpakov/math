import OAI.AlgebraicGeometry.DivisorClass.Chern.ThomCupIntrinsicTest
import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.ThomIso

/-! # Thom Intrinsic Cup -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.ThomIntrinsicCup

noncomputable section

/-! The original compactly supported cup factors through the actual compact source Thom isomorphism. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

theorem regularThomCompactIntersection_le (K : Compacts D.regularAmbientSpace) :
    ThomIso.regularThomCompactIntersection D K ≤ K := Set.inter_subset_left

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)

theorem regularSheafCompactThomCup_forget (K : Compacts D.regularAmbientSpace) (n : ℕ) :
    ThomIso.regularSheafCompactThomCup D a K n ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) (regularThomCompactIntersection_le D K) (2+n) =
    ModuleCat.ofHom (CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup (R := ℚ) (TopCat.of D.regularAmbientSpace)
      (K : Set D.regularAmbientSpace)ᶜ 2 n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (D.regularThomComplementOpen : Set D.regularAmbientSpace) 2 (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a))) := by
  let O := SourceSheafTrace.compactTestComplement (X := TopCat.of D.regularAmbientSpace) K
  have hc := AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap_source_congr (TopCat.of D.regularAmbientSpace)
    (ThomIso.regularThomCompactIntersection_complement D K)
    (Set.subset_union_left : (O : Set D.regularAmbientSpace) ⊆
      (O ⊔ D.regularThomComplementOpen : Opens D.regularAmbientSpace))
    (Set.compl_subset_compl.mpr (regularThomCompactIntersection_le D K)) (2+n)
  change (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAmbientSpace)
    (ThomIso.regularThomCompactIntersection_complement D K) (2+n)).hom ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) (regularThomCompactIntersection_le D K) (2+n) = _ at hc
  change (ThomCupIntrinsicTest.regularSupportedThomRelativeCup D a O n ≫
    (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAmbientSpace)
      (ThomIso.regularThomCompactIntersection_complement D K) (2+n)).hom) ≫ _ = _
  rw [Category.assoc, hc]
  exact ThomCupIntrinsicTest.regularSupportedThomCup_native_test D a O n

theorem regularSheafCompactThomCup_compact (K : Compacts D.regularAmbientSpace) (n : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (K : Set D.regularAmbientSpace)ᶜ n) :
    HodgeConjecture.DegreeTwo.CompactLeftCup.Constructions.compactCohomologyLeftCup (TopCat.of D.regularAmbientSpace) 2 n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (D.regularThomComplementOpen : Set D.regularAmbientSpace) 2 (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a))
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace) K n b) =
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (ThomIso.regularThomCompactIntersection D K) (2+n) (ThomIso.regularSheafCompactThomCup D a K n b) := by
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap_ι (ModuleCat.of ℚ ℚ) (regularThomCompactIntersection_le D K) (2+n))
    (ThomIso.regularSheafCompactThomCup D a K n b)
  have hc := ConcreteCategory.congr_hom (regularSheafCompactThomCup_forget D a K n) b
  simp only [ConcreteCategory.comp_apply] at h hc
  have hh := (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
    (TopCat.of D.regularAmbientSpace) K (2+n)) hc.symm).trans h
  exact (HodgeConjecture.DegreeTwo.CompactLeftCup.Constructions.compactCohomologyLeftCup_stage (TopCat.of D.regularAmbientSpace) 2 n
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (D.regularThomComplementOpen : Set D.regularAmbientSpace) 2 (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a)) K b).trans hh

theorem regularSourceCompactThomIso_cup (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)
    (K : Compacts D.regularAmbientSpace) (n : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (K : Set D.regularAmbientSpace)ᶜ n) :
    HodgeConjecture.DegreeTwo.CompactLeftCup.Constructions.compactCohomologyLeftCup (TopCat.of D.regularAmbientSpace) 2 n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (D.regularThomComplementOpen : Set D.regularAmbientSpace) 2 D.regularThomClass)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace) K n b) =
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (ThomIso.regularThomCompactIntersection D K) (2+n)
      ((ThomIso.regularSourceCompactThomIso D a ha K n).hom
        (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap
          D.isProperMap_regularComplementTopCatMap K n b)) := by
  have h := regularSheafCompactThomCup_compact D a K n b
  rw [ha] at h
  have hc := ConcreteCategory.congr_hom (ThomIso.regularSheafCompactThomCup_factorization D a ha K n) b
  simp only [ConcreteCategory.comp_apply] at hc
  exact h.trans (congrArg
    (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (ThomIso.regularThomCompactIntersection D K) (2+n)) hc.symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.ThomIntrinsicCup
