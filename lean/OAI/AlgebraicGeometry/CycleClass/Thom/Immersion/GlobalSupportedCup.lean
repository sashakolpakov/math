import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedSourceCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTopPullback
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedThomSource

/-! # Global Supported Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSupportedCup.Constructions.Construction

noncomputable section

/-! The supported global source–Thom isomorphism intertwines actual relative pullback with the original global two-support cup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTopPullback.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceThomSupportedGlobalIso_cup (O : Opens Z.regularAmbientSpace) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)
      (A := (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace))
      (B := (O : Set Z.regularAmbientSpace)) (fun _ hx => hx) q ≫
        (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha O q).hom =
    ModuleCat.ofHom (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of Z.regularAmbientSpace)
      (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) (O : Set Z.regularAmbientSpace)
      Z.regularThomComplementOpen.isOpen O.isOpen (2 * p) q Z.regularThomClass) := by
  exact HodgeConjecture.DegreeTwo.LocalSupportCup.Constructions.supportConjugateIso_cup
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      (O : Set Z.regularAmbientSpace) q)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace) q)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) ((2 * p)+q))
    (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso Z a ha O ⊤ q) _ _ _ _
    (HodgeConjecture.DegreeTwo.RelativeTopPullback.Constructions.relativeSourcePullbackMap_top_comparison (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) O q)
    (HodgeConjecture.DegreeTwo.RelativeTopPullback.Constructions.twoSupportCup_top_comparison (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen O (2 * p) q Z.regularThomClass)
    (SupportedSourceCup.Constructions.Construction.regularSourceThomSupportedRelativeIso_cup Z a ha O ⊤ q)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSupportedCup.Constructions.Construction
