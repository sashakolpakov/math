import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedSourceNaturality
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedThomSource

/-! # Global Source Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSourceNaturality.Constructions.Construction

noncomputable section

/-! The actual global source-relative Thom isomorphisms respect support enlargement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceThomSupportedGlobalIso_support_naturality
    {C D : Opens Z.regularAmbientSpace} (h : C ≤ D) (n : ℕ) :
    HomologicalComplex.homologyMap
        (HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions.relativeComplementChange (TopCat.of Z.regularAnalyticSpace)
          (show ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj C : Set Z.regularAnalyticSpace) ⊆
            ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj D : Set Z.regularAnalyticSpace)
            from fun _ hx => h hx)) n ≫
        (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha C n).hom =
      (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha D n).hom ≫
        HomologicalComplex.homologyMap
          (HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions.relativeComplementChange (TopCat.of Z.regularAmbientSpace)
            (show ((Z.regularThomComplementOpen ⊔ C : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) ⊆
              ((Z.regularThomComplementOpen ⊔ D : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace)
              from sup_le_sup_left h Z.regularThomComplementOpen)) ((2 * p)+n) := by
  exact SupportedSourceNaturality.Constructions.Construction.sourceTargetIso_naturality
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj D : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace) n)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj C : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace) n)
    (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso Z a ha D ⊤ n)
    (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso Z a ha C ⊤ n)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      ((Z.regularThomComplementOpen ⊔ D : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) ((2 * p)+n))
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      ((Z.regularThomComplementOpen ⊔ C : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) ((2 * p)+n)) _ _ _ _
    (HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions.relativeCohomologyPresheafTopIso_support_naturality (TopCat.of Z.regularAnalyticSpace)
      (show (Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj C ≤ (Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj D
        from fun _ hx => h hx) n)
    (SupportedSourceNaturality.Constructions.Construction.regularSourceThomSupportedRelativeIso_support_naturality Z a ha h ⊤ n)
    (HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions.relativeCohomologyPresheafTopIso_support_naturality (TopCat.of Z.regularAmbientSpace)
      (sup_le_sup_left h Z.regularThomComplementOpen) ((2 * p)+n))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSourceNaturality.Constructions.Construction
