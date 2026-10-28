import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.SourceCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTopPullback
import OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSupportedSource

/-! # Global Supported Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSupportedCup.Constructions.HigherThom

noncomputable section

/-! The supported global source–Thom isomorphism intertwines actual relative pullback with the original global two-support cup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTopPullback.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceThomSupportedGlobalIso_cup (O : Opens Z.regularAmbientSpace) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)
      (A := (((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace))
      (B := (O : Set Z.regularAmbientSpace)) (fun _ hx => hx) q ≫
        (GlobalSupportedSource.Constructions.HigherThom.regularSourceThomSupportedGlobalIso Z a ha O q).hom =
    ModuleCat.ofHom (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of Z.regularAmbientSpace)
      (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) (O : Set Z.regularAmbientSpace)
      Z.regularThomComplementOpen.isOpen O.isOpen (2 * p) q Z.regularThomClass) := by
  exact HodgeConjecture.DegreeTwo.LocalSupportCup.Constructions.supportConjugateIso_cup
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      (O : Set Z.regularAmbientSpace) q)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace) q)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) ((2 * p)+q))
    (Supported.SourceIso.Constructions.HigherThom.regularSourceThomSupportedRelativeIso Z a ha O ⊤ q) _ _ _ _
    (HodgeConjecture.DegreeTwo.RelativeTopPullback.Constructions.relativeSourcePullbackMap_top_comparison (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) O q)
    (HodgeConjecture.DegreeTwo.RelativeTopPullback.Constructions.twoSupportCup_top_comparison (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen O (2 * p) q Z.regularThomClass)
    (Supported.SourceCup.Constructions.HigherThom.regularSourceThomSupportedRelativeIso_cup Z a ha O ⊤ q)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSupportedCup.Constructions.HigherThom
