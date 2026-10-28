import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedSourceThomNaturality
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GlobalSupportedSourceThom

/-! # Global Source Thom Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GlobalSourceThomNaturality.Constructions

noncomputable section

/-! The actual global source-relative Thom isomorphisms respect support enlargement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceThomSupportedGlobalIso_support_naturality
    {C D : Opens Z.regularAmbientSpace} (h : C ≤ D) (n : ℕ) :
    HomologicalComplex.homologyMap
        (RelativeTopSupportNaturality.Constructions.relativeComplementChange (TopCat.of Z.regularAnalyticSpace)
          (show ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj C : Set Z.regularAnalyticSpace) ⊆
            ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj D : Set Z.regularAnalyticSpace)
            from fun _ hx => h hx)) n ≫
        (GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso Z a ha C n).hom =
      (GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso Z a ha D n).hom ≫
        HomologicalComplex.homologyMap
          (RelativeTopSupportNaturality.Constructions.relativeComplementChange (TopCat.of Z.regularAmbientSpace)
            (show ((Z.regularThomComplementOpen ⊔ C : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) ⊆
              ((Z.regularThomComplementOpen ⊔ D : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace)
              from sup_le_sup_left h Z.regularThomComplementOpen)) (2+n) := by
  exact SupportedSourceThomNaturality.Constructions.sourceTargetIso_naturality
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj D : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace) n)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj C : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace) n)
    (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha D ⊤ n)
    (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha C ⊤ n)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      ((Z.regularThomComplementOpen ⊔ D : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) (2+n))
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      ((Z.regularThomComplementOpen ⊔ C : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) (2+n)) _ _ _ _
    (RelativeTopSupportNaturality.Constructions.relativeCohomologyPresheafTopIso_support_naturality (TopCat.of Z.regularAnalyticSpace)
      (show (Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj C ≤ (Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj D
        from fun _ hx => h hx) n)
    (SupportedSourceThomNaturality.Constructions.regularSourceThomSupportedRelativeIso_support_naturality Z a ha h ⊤ n)
    (RelativeTopSupportNaturality.Constructions.relativeCohomologyPresheafTopIso_support_naturality (TopCat.of Z.regularAmbientSpace)
      (sup_le_sup_left h Z.regularThomComplementOpen) (2+n))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GlobalSourceThomNaturality.Constructions
