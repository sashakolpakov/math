import OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupPresheaf
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupSheaf

/-! # Even Cup Sheaf -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupSheaf.Constructions

noncomputable section

/-! Actual cup multiplication on the supported singular sheaf complex. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (O : Opens X)

variable {p : ℕ}
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)) (2 * p))

def relativeEvenCupToSupportedPresheafComplexMap :
    AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X ⟶
      AlgebraicTopology.Cohomology.Singular.SheafSections.sheafUnderlyingCochainComplex
        ((Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).restriction
          (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p))) :=
  EvenCupPresheaf.Constructions.relativeEvenCupPresheafComplexMap X (O : Set X) a ≫
    HomologicalComplex.restrictionMap (HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeToSupportedPresheafComplexMap X O)
      (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p))

/-- This is a map of genuine sheaf complexes, induced by the original singular cup. -/
def relativeEvenCupSheafMap :
    AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) ⟶
      (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).restriction
        (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p)) :=
  HodgeConjecture.DegreeTwo.SheafComplexLift.Constructions.sheafComplexLift (relativeEvenCupToSupportedPresheafComplexMap X O a)

def relativeEvenCupGoodShiftSheafMap :
    AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) ⟶
      (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).truncGE'
        (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p)) :=
  relativeEvenCupSheafMap X O a ≫
    (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).restrictionToTruncGE'
      (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p))

def relativeEvenCupSheafSectionsMap (U : Opens X) :
    AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularSheafSections (ModuleCat.of ℚ ℚ) X U ⟶
      (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSections (ModuleCat.of ℚ ℚ) X O U).restriction
        (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p)) :=
  ((Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (relativeEvenCupSheafMap X O a)

/-- On every open set the actual unit intertwines sheaf cup with singular cup. -/
theorem relativeEvenCupSheafSectionsMap_unit (U : Opens X) :
    AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U ≫
        relativeEvenCupSheafSectionsMap X O a U =
      EvenCupPresheaf.Constructions.relativeEvenCupOpenCochainMap X (O : Set X) a U ≫
        HomologicalComplex.restrictionMap
          (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X O U)
          (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p)) := by
  ext n : 1
  exact NatTrans.congr_app
    (HodgeConjecture.DegreeTwo.SheafComplexLift.Constructions.sheafComplexLift_unit (relativeEvenCupToSupportedPresheafComplexMap X O a) n) (op U)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupSheaf.Constructions
