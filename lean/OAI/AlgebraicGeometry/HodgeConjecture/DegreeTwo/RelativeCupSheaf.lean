import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SheafComplexLift
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupPresheaf

/-! # Relative Cup Sheaf -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions

noncomputable section

/-! Actual cup multiplication on the supported singular sheaf complex. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (O : Opens X)

def relativeToSupportedPresheafComplexMap :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafComplex (ModuleCat.of ℚ ℚ) X (O : Set X) ⟶
      AlgebraicTopology.Cohomology.Singular.SheafSections.sheafUnderlyingCochainComplex (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O) where
  f n :=
    { app U := (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X O U.unop).f n
      naturality U W i := congrArg (fun f => f.f n)
        ((AlgebraicTopology.Cohomology.Singular.RelativeSupportedNaturality.relativeToSupportedSheafPresheafMap (ModuleCat.of ℚ ℚ) X O).naturality i) }
  comm' i j hij := by
    apply NatTrans.ext
    funext U
    exact (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X O U.unop).comm' i j hij

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)) 2)

def relativeTwoCupToSupportedPresheafComplexMap :
    AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X ⟶
      AlgebraicTopology.Cohomology.Singular.SheafSections.sheafUnderlyingCochainComplex
        ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).restriction
          (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2)) :=
  RelativeCupPresheaf.Constructions.relativeTwoCupPresheafComplexMap X (O : Set X) a ≫
    HomologicalComplex.restrictionMap (relativeToSupportedPresheafComplexMap X O)
      (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2)

/-- This is a map of genuine sheaf complexes, induced by the original singular cup. -/
def relativeTwoCupSheafMap :
    AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) ⟶
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).restriction
        (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2) :=
  SheafComplexLift.Constructions.sheafComplexLift (relativeTwoCupToSupportedPresheafComplexMap X O a)

def relativeTwoCupGoodShiftSheafMap :
    AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) ⟶
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).truncGE'
        (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2) :=
  relativeTwoCupSheafMap X O a ≫
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O).restrictionToTruncGE'
      (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2)

def relativeTwoCupSheafSectionsMap (U : Opens X) :
    AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularSheafSections (ModuleCat.of ℚ ℚ) X U ⟶
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSections (ModuleCat.of ℚ ℚ) X O U).restriction
        (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2) :=
  ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (relativeTwoCupSheafMap X O a)

/-- On every open set the actual unit intertwines sheaf cup with singular cup. -/
theorem relativeTwoCupSheafSectionsMap_unit (U : Opens X) :
    AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U ≫
        relativeTwoCupSheafSectionsMap X O a U =
      RelativeCupPresheaf.Constructions.relativeTwoCupOpenCochainMap X (O : Set X) a U ≫
        HomologicalComplex.restrictionMap
          (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X O U)
          (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2) := by
  ext n : 1
  exact NatTrans.congr_app
    (SheafComplexLift.Constructions.sheafComplexLift_unit (relativeTwoCupToSupportedPresheafComplexMap X O a) n) (op U)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions
