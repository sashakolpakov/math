import OAI.AlgebraicGeometry.ComplexMultiplication.CMGlobalSheafCycles

/-! # Global Filtration -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalFiltration

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint
open scoped OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint

/-! # Genuine global holomorphic classes lie in the unchanged original filtration -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

/-- An isomorphism on actual cycles is surjective on their cohomology classes. -/
theorem homologyMap_epi_of_cycles_isIso {K L : CochainComplex AddCommGrpCat ℤ}
    (f : K ⟶ L) (p : ℤ) [IsIso (HomologicalComplex.cyclesMap f p)] :
    Epi (HomologicalComplex.homologyMap f p) :=
  epi_of_epi_fac (HomologicalComplex.homologyπ_naturality f p)

/-- Every full global cohomology class in the filtration degree has an actual
class lift through the original degree truncation. -/
theorem globalStupidTruncInclusion_homology_surjective (Y : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) (p : ℤ) :
    Function.Surjective (HomologicalComplex.homologyMap
      ((Functor.mapHomologicalComplex
        (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y)
          (ComplexShape.up ℤ)).map
            (Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncInclusion K (ComplexShape.embeddingUpIntGE p))) p) := by
  have := CMGlobalSheafCycles.globalStupidTruncInclusion_cycles_isIso Y K p
  have := homologyMap_epi_of_cycles_isIso
    ((Functor.mapHomologicalComplex
      (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y)
        (ComplexShape.up ℤ)).map
          (Algebra.Homology.StupidTruncation.HomologicalComplex.stupidTruncInclusion K (ComplexShape.embeddingUpIntGE p))) p
  exact (AddCommGrpCat.epi_iff_surjective _).1 inferInstance

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

set_option backward.isDefEq.respectTransparency false in
/-- The class of every actual global holomorphic cohomology element lies in
the original filtration in its form degree. -/
theorem originalGlobalDeRhamClass_mem_filtration (p : ℤ)
    (z : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) Ω•(X)).homology p) :
    GlobalNaturality.globalSectionsToHypercohomology X Ω•(X) p z ∈ ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration X p p := by
  obtain ⟨w, hw⟩ := globalStupidTruncInclusion_homology_surjective
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) Ω•(X) p z
  apply (FilteredGlobalClasses.originalHodgeFiltration_mem_iff_globalClass X p _).2
  refine ⟨w, ?_⟩
  change ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion X p) p
    (GlobalNaturality.globalSectionsToHypercohomology X (F^p Ω•(X)) p w) =
      GlobalNaturality.globalSectionsToHypercohomology X Ω•(X) p z
  have hn := GlobalNaturality.globalSectionsToHypercohomology_naturality X
    (ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion X p) p w
  change HomologicalComplex.homologyMap
    (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (ComplexPoint.Basic.ComplexSchemePoint.hodgeFilteredDeRhamInclusion X p)) p w = z at hw
  rw [hw] at hn
  exact hn.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalFiltration
