import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTopPullback
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GlobalSupportedSourceThom

/-! # Global Supported Thom Cup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GlobalSupportedThomCup.Constructions

noncomputable section

/-! The supported global source–Thom isomorphism intertwines actual relative pullback with the original global two-support cup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceThomSupportedGlobalIso_cup (O : Opens Z.regularAmbientSpace) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)
      (A := (((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace))
      (B := (O : Set Z.regularAmbientSpace)) (fun _ hx => hx) q ≫
        (GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso Z a ha O q).hom =
    ModuleCat.ofHom (SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of Z.regularAmbientSpace)
      (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) (O : Set Z.regularAmbientSpace)
      Z.regularThomComplementOpen.isOpen O.isOpen 2 q Z.regularThomClass) := by
  exact LocalSupportCup.Constructions.supportConjugateIso_cup
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      (O : Set Z.regularAmbientSpace) q)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace) q)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) (2+q))
    (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha O ⊤ q) _ _ _ _
    (RelativeTopPullback.Constructions.relativeSourcePullbackMap_top_comparison (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) O q)
    (RelativeTopPullback.Constructions.twoSupportCup_top_comparison (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen O 2 q Z.regularThomClass)
    (NormalSupportRelative.Constructions.regularSourceThomSupportedRelativeIso_cup Z a ha O ⊤ q)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GlobalSupportedThomCup.Constructions
