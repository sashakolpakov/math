import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupShiftSections
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomology

/-! # Supported Cup Section Cohomology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedCupSectionCohomology.Constructions

noncomputable section

/-! The actual sheaf cup on sections induces the original relative cup in every shifted degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (O : Opens X)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)) 2)

def relativeTwoCupGoodShiftSheafSectionsMap (U : Opens X) :=
  ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap X O a)

theorem relativeTwoCupGoodShiftSheafSectionsMap_unit (U : Opens X) :
    AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U ≫
        relativeTwoCupGoodShiftSheafSectionsMap X O a U =
      ((AlgebraicTopology.Cohomology.Singular.Stalk.presheafSectionFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (RelativeCupShiftSections.Constructions.relativeTwoCupGoodShiftPresheafMap X O a) := by
  unfold relativeTwoCupGoodShiftSheafSectionsMap
  rw [← RelativeCupShiftSections.Constructions.relativeTwoCupGoodShiftPresheafMap_lift]
  ext n : 1
  exact NatTrans.congr_app (SheafComplexLift.Constructions.sheafComplexLift_unit (RelativeCupShiftSections.Constructions.relativeTwoCupGoodShiftPresheafMap X O a) n) (op U)

variable [MetrizableSpace X]
variable (he : ∀ n, n<2 →
  (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).ExactAt n)

def supportedTwoGoodShiftRelativeIso (U : Opens X) (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).truncGE'
      (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2))).homology n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) U) (2+n) := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable ℚ X O U
  exact GoodShiftComparison.Constructions.cochainGoodShiftComparisonIso
    (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X O U) 2 n
    (RelativeCupShiftSections.Constructions.supportedTwoGoodShiftSectionsIso X O he U)

theorem relativeTwoCupGoodShiftPresheafMap_cohomology (U : Opens X) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((AlgebraicTopology.Cohomology.Singular.Stalk.presheafSectionFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (RelativeCupShiftSections.Constructions.relativeTwoCupGoodShiftPresheafMap X O a)) n ≫
        (supportedTwoGoodShiftRelativeIso X O he U n).hom =
      ModuleCat.ofHom (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) U) 2 n
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X (O : Set X) a U))) := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable ℚ X O U
  rw [RelativeCupShiftSections.Constructions.relativeTwoCupGoodShiftPresheafMap_sections X O a he U]
  exact (GoodShiftComparison.Constructions.cochainGoodShiftComparisonIso_transport
    (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X O U) 2 n
    (RelativeCupShiftSections.Constructions.supportedTwoGoodShiftSectionsIso X O he U)
    (RelativeCupHomotopy.Constructions.relativeTwoCupGoodShiftMap (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) U)
      (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X (O : Set X) a U))).trans
        (RelativeCupHomology.Constructions.relativeTwoCupGoodShiftHomology_eq _ _ _ n)

theorem relativeTwoCupGoodShiftSheafSections_cohomology (U : Opens X) (n : ℕ) :
    HomologicalComplex.homologyMap
        (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U) n ≫
      HomologicalComplex.homologyMap (relativeTwoCupGoodShiftSheafSectionsMap X O a U) n ≫
        (supportedTwoGoodShiftRelativeIso X O he U n).hom =
      ModuleCat.ofHom (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) U) 2 n
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X (O : Set X) a U))) := by
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    relativeTwoCupGoodShiftSheafSectionsMap_unit]
  exact relativeTwoCupGoodShiftPresheafMap_cohomology X O a he U n

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedCupSectionCohomology.Constructions
