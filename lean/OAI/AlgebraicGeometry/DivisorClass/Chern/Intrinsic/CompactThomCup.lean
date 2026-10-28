import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.CompactThomStage
import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.ThomIntrinsicCup

/-! # Compact Thom Cup -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.CompactThomCup

noncomputable section

/-! The original compact cup with the original Thom class is proper pullback followed by the native Thom pushforward. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem relativeCohomologyCongr_compactι (X : TopCat.{0}) {K L : Compacts X} (e : K = L) (n : ℕ) :
    (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr X (congrArg (fun J : Compacts X => (J : Set X)ᶜ) e) n).hom ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X L n =
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K n := by
  subst L
  exact Category.id_comp _

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)

theorem regularSourceCompactThomIso_pushforward (K : Compacts D.regularAmbientSpace) (n : ℕ) :
    (Compact.ThomIso.regularSourceCompactThomIso D a ha K n).hom ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (Compact.ThomIso.regularThomCompactIntersection D K) (2+n) =
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAnalyticSpace)
      (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage D.regularComplementTopCatMap D.isProperMap_regularComplementTopCatMap K) n ≫
      HodgeConjecture.DegreeTwo.CompactThomZero.Constructions.regularSourceCompactThomPushforward D a ha n := by
  rw [CompactThomStage.regularSourceCompactThomIso_native, Iso.trans_hom, Category.assoc,
    relativeCohomologyCongr_compactι _ (Compact.ImageSupport.regularCompactImage_preimage D K),
    HodgeConjecture.DegreeTwo.CompactThomZero.Constructions.regularSourceCompactThomPushforward_stage]

theorem regularSourceCompactThomPushforward_cup (n : ℕ)
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace) n) :
    HodgeConjecture.DegreeTwo.CompactLeftCup.Constructions.compactCohomologyLeftCup (TopCat.of D.regularAmbientSpace) 2 n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (D.regularThomComplementOpen : Set D.regularAmbientSpace) 2 D.regularThomClass) b =
    HodgeConjecture.DegreeTwo.CompactThomZero.Constructions.regularSourceCompactThomPushforward D a ha n
      (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap
        D.isProperMap_regularComplementTopCatMap n b) := by
  obtain ⟨K, c, rfl⟩ := AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_exists_stage (ModuleCat.of ℚ ℚ)
    (TopCat.of D.regularAmbientSpace) n b
  rw [Compact.ThomIntrinsicCup.regularSourceCompactThomIso_cup D a ha]
  have hs := ConcreteCategory.congr_hom (regularSourceCompactThomIso_pushforward D a ha K n)
    (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap
      D.isProperMap_regularComplementTopCatMap K n c)
  have hp := ConcreteCategory.congr_hom (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportCohomologyι_properPullback
    (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap D.isProperMap_regularComplementTopCatMap K n) c
  simp only [ConcreteCategory.comp_apply] at hs hp
  exact hs.trans (congrArg (HodgeConjecture.DegreeTwo.CompactThomZero.Constructions.regularSourceCompactThomPushforward D a ha n) hp.symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.CompactThomCup
