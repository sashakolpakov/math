import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupSheaf
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomShiftSections

/-! # Relative Cup Shift Sections -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupShiftSections.Constructions

noncomputable section

/-! The actual sheaf cup agrees on sections with the canonical shifted relative cup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}}

theorem rationalFlasqueGoodShiftSectionsIso_projection
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (k : ℕ)
    (he : ∀ n, n<k → K.ExactAt n) (U : Opens X) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U K).restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) ≫
        (ThomShiftSections.Constructions.rationalFlasqueGoodShiftSectionsIso K hK k he U).hom =
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) :=
  GoodShiftComparison.Constructions.goodShiftFunctorIso_projection (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U) K k _

variable (X) (O : Opens X)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)) 2)

theorem relativeTwoCocycleOpenRestriction_class (U : Opens X) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X (O : Set X) a U) =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) X (O : Set X) U 2
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a) :=
  (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
    (Opens.inclusion' U) (fun _ hx => hx)) 2 a).symm

def relativeTwoCupGoodShiftPresheafMap :
    AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X ⟶
      AlgebraicTopology.Cohomology.Singular.SheafSections.sheafUnderlyingCochainComplex
        ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).truncGE'
          (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2)) :=
  RelativeCupSheaf.Constructions.relativeTwoCupToSupportedPresheafComplexMap X O a ≫
    ((TopCat.Sheaf.forget (ModuleCat.{0} ℚ) X).mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).restrictionToTruncGE'
        (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2))

theorem relativeTwoCupGoodShiftPresheafMap_lift :
    SheafComplexLift.Constructions.sheafComplexLift (relativeTwoCupGoodShiftPresheafMap X O a) =
      RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap X O a :=
  GoodShiftComparison.Constructions.sheafComplexLift_postcomp _ _

variable [MetrizableSpace X]
variable (he : ∀ n, n<2 →
  (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).ExactAt n)

def supportedTwoGoodShiftSectionsIso (U : Opens X) :=
  ThomShiftSections.Constructions.rationalFlasqueGoodShiftSectionsIso
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O)
    (CycleClass.Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) X O) 2 he U

theorem relativeTwoCupGoodShiftPresheafMap_sections (U : Opens X) :
    ((AlgebraicTopology.Cohomology.Singular.Stalk.presheafSectionFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (relativeTwoCupGoodShiftPresheafMap X O a) =
      RelativeCupHomotopy.Constructions.relativeTwoCupGoodShiftMap (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) U)
          (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X (O : Set X) a U) ≫
        HomologicalComplex.truncGE'Map
          (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X O U)
          (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2) ≫
        (supportedTwoGoodShiftSectionsIso X O he U).hom := by
  unfold RelativeCupHomotopy.Constructions.relativeTwoCupGoodShiftMap
  rw [Category.assoc, HomologicalComplex.restrictionToTruncGE'_naturality_assoc]
  have hp : (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSections (ModuleCat.of ℚ ℚ) X O U).restrictionToTruncGE'
      (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2) ≫ (supportedTwoGoodShiftSectionsIso X O he U).hom =
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).restrictionToTruncGE'
        (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2)) :=
    rationalFlasqueGoodShiftSectionsIso_projection _ _ _ _ _
  rw [hp]
  ext n : 1
  rfl

include he

theorem relativeTwoCupGoodShiftPresheafMap_open_quasiIso (U : Opens X)
    (ha : QuasiIso (RelativeCupHomotopy.Constructions.relativeTwoCupGoodShiftMap (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) U)
      (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X (O : Set X) a U))) :
    QuasiIso (((AlgebraicTopology.Cohomology.Singular.Stalk.presheafSectionFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (relativeTwoCupGoodShiftPresheafMap X O a)) := by
  rw [relativeTwoCupGoodShiftPresheafMap_sections X O a he U]
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable ℚ X O U
  have := GoodShiftComparison.Constructions.cochainGoodShiftMap_quasiIso
    (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X O U) 2
  infer_instance

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupShiftSections.Constructions
