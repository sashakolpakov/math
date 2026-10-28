import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedThomRelative
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportThomResolution
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportIs

/-! # Supported Source Thom Iso -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedSourceThomIso.Constructions

noncomputable section

/-! The source–Thom isomorphism with a prescribed closed support, on the original relative groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

def regularSourceThomSupportedRelativeIso (O U : Opens Z.regularAmbientSpace) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAnalyticSpace)
        (((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) :
          Set Z.regularAnalyticSpace) ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
        ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) U)
      (2+n) :=
  (ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) O U n).symm ≪≫
    ClosedSupportThomResolution.Constructions.regularSourceThomClosedSupportIso Z a ha O U n ≪≫ SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso Z O U n

theorem regularSourceThomSupportedRelativeIso_eq
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
    (hb : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 b = Z.regularThomClass) (O U : Opens Z.regularAmbientSpace) (n : ℕ) :
    regularSourceThomSupportedRelativeIso Z a ha O U n =
      regularSourceThomSupportedRelativeIso Z b hb O U n := by
  unfold regularSourceThomSupportedRelativeIso
  rw [ClosedSupportThomResolution.Constructions.regularSourceThomClosedSupportIso_eq Z a ha b hb]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedSourceThomIso.Constructions
