import OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupSheaf
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupShiftSections

/-! # Even Cup Shift Sections -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupShiftSections.Constructions

noncomputable section

/-! The actual sheaf cup agrees on sections with the canonical shifted relative cup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupShiftSections.Constructions

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}}

variable (X) (O : Opens X)
variable {p : ℕ}
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)) (2 * p))

theorem relativeEvenCocycleOpenRestriction_class (U : Opens X) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) (EvenCupPresheaf.Constructions.relativeEvenCocycleOpenRestriction X (O : Set X) a U) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) X (O : Set X) U (2 * p)
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a) :=
  (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
    (Opens.inclusion' U) (fun _ hx => hx)) (2 * p) a).symm

def relativeEvenCupGoodShiftPresheafMap :
    AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X ⟶
      AlgebraicTopology.Cohomology.Singular.SheafSections.sheafUnderlyingCochainComplex
        ((Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).truncGE'
          (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p))) :=
  EvenCupSheaf.Constructions.relativeEvenCupToSupportedPresheafComplexMap X O a ≫
    ((TopCat.Sheaf.forget (ModuleCat.{0} ℚ) X).mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).restrictionToTruncGE'
        (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p)))

theorem relativeEvenCupGoodShiftPresheafMap_lift :
    HodgeConjecture.DegreeTwo.SheafComplexLift.Constructions.sheafComplexLift (relativeEvenCupGoodShiftPresheafMap X O a) =
      EvenCupSheaf.Constructions.relativeEvenCupGoodShiftSheafMap X O a :=
  HodgeConjecture.DegreeTwo.GoodShiftComparison.Constructions.sheafComplexLift_postcomp _ _

variable [MetrizableSpace X]
variable (he : ∀ n, n<(2 * p) →
  (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).ExactAt n)

def supportedEvenGoodShiftSectionsIso (U : Opens X) :=
  HodgeConjecture.DegreeTwo.ThomShiftSections.Constructions.rationalFlasqueGoodShiftSectionsIso
    (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O)
    (Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) X O) (2 * p) he U

theorem relativeEvenCupGoodShiftPresheafMap_sections (U : Opens X) :
    ((AlgebraicTopology.Cohomology.Singular.Stalk.presheafSectionFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (relativeEvenCupGoodShiftPresheafMap X O a) =
      EvenCupComplex.Constructions.relativeEvenCupGoodShiftMap (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) U)
          (EvenCupPresheaf.Constructions.relativeEvenCocycleOpenRestriction X (O : Set X) a U) ≫
        HomologicalComplex.truncGE'Map
          (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X O U)
          (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p)) ≫
        (supportedEvenGoodShiftSectionsIso X O he U).hom := by
  unfold EvenCupComplex.Constructions.relativeEvenCupGoodShiftMap
  rw [Category.assoc, HomologicalComplex.restrictionToTruncGE'_naturality_assoc]
  have hp : (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSections (ModuleCat.of ℚ ℚ) X O U).restrictionToTruncGE'
      (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p)) ≫ (supportedEvenGoodShiftSectionsIso X O he U).hom =
    ((Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).restrictionToTruncGE'
        (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p))) :=
    HodgeConjecture.DegreeTwo.RelativeCupShiftSections.Constructions.rationalFlasqueGoodShiftSectionsIso_projection _ _ _ _ _
  rw [hp]
  ext n : 1
  rfl

include he

theorem relativeEvenCupGoodShiftPresheafMap_open_quasiIso (U : Opens X)
    (ha : QuasiIso (EvenCupComplex.Constructions.relativeEvenCupGoodShiftMap (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) U)
      (EvenCupPresheaf.Constructions.relativeEvenCocycleOpenRestriction X (O : Set X) a U))) :
    QuasiIso (((AlgebraicTopology.Cohomology.Singular.Stalk.presheafSectionFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (relativeEvenCupGoodShiftPresheafMap X O a)) := by
  rw [relativeEvenCupGoodShiftPresheafMap_sections X O a he U]
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable ℚ X O U
  have := HodgeConjecture.DegreeTwo.GoodShiftComparison.Constructions.cochainGoodShiftMap_quasiIso
    (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X O U) (2 * p)
  infer_instance

end

end OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupShiftSections.Constructions
