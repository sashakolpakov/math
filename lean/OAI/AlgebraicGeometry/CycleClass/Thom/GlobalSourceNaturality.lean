import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.SourceNaturality
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSupportedSource

/-! # Global Source Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSourceNaturality.Constructions.HigherThom

noncomputable section

/-! The actual global source-relative Thom isomorphisms respect support enlargement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceThomSupportedGlobalIso_support_naturality
    {C D : Opens Z.regularAmbientSpace} (h : C ≤ D) (n : ℕ) :
    HomologicalComplex.homologyMap
        (HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions.relativeComplementChange (TopCat.of Z.regularAnalyticSpace)
          (show ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj C : Set Z.regularAnalyticSpace) ⊆
            ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj D : Set Z.regularAnalyticSpace)
            from fun _ hx => h hx)) n ≫
        (GlobalSupportedSource.Constructions.HigherThom.regularSourceThomSupportedGlobalIso Z a ha C n).hom =
      (GlobalSupportedSource.Constructions.HigherThom.regularSourceThomSupportedGlobalIso Z a ha D n).hom ≫
        HomologicalComplex.homologyMap
          (HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions.relativeComplementChange (TopCat.of Z.regularAmbientSpace)
            (show ((Z.regularThomComplementOpen ⊔ C : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) ⊆
              ((Z.regularThomComplementOpen ⊔ D : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace)
              from sup_le_sup_left h Z.regularThomComplementOpen)) ((2 * p)+n) := by
  exact Supported.SourceNaturality.Constructions.HigherThom.sourceTargetIso_naturality
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj D : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace) n)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj C : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace) n)
    (Supported.SourceIso.Constructions.HigherThom.regularSourceThomSupportedRelativeIso Z a ha D ⊤ n)
    (Supported.SourceIso.Constructions.HigherThom.regularSourceThomSupportedRelativeIso Z a ha C ⊤ n)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      ((Z.regularThomComplementOpen ⊔ D : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) ((2 * p)+n))
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      ((Z.regularThomComplementOpen ⊔ C : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) ((2 * p)+n)) _ _ _ _
    (HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions.relativeCohomologyPresheafTopIso_support_naturality (TopCat.of Z.regularAnalyticSpace)
      (show (Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj C ≤ (Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj D
        from fun _ hx => h hx) n)
    (Supported.SourceNaturality.Constructions.HigherThom.regularSourceThomSupportedRelativeIso_support_naturality Z a ha h ⊤ n)
    (HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions.relativeCohomologyPresheafTopIso_support_naturality (TopCat.of Z.regularAmbientSpace)
      (sup_le_sup_left h Z.regularThomComplementOpen) ((2 * p)+n))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSourceNaturality.Constructions.HigherThom
