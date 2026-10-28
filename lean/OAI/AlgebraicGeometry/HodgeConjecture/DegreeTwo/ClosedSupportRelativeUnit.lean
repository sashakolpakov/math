import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap

/-! # Closed Support Relative Unit -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit.Constructions

noncomputable section

/-! The original relative cochains map to the closed-support functor through the actual sheafification unit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (O U : Opens X)

def relativeToClosedSupportSections :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U) ⟶
    GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) :=
  AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X O U ≫
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (ClosedSupportIs.Constructions.closedSupportFunctorComplexIso O (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).hom

theorem relativeToClosedSupportSections_inclusion :
    relativeToClosedSupportSections O U ≫ ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion O U (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U) ≫
        AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U := by
  unfold relativeToClosedSupportSections ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion
  rw [Category.assoc, ← Functor.map_comp, ClosedSupportIs.Constructions.closedSupportFunctorComplexIso_inclusion]
  exact AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections_inclusion (ModuleCat.of ℚ ℚ) X O U

variable [MetrizableSpace X]

instance relativeToClosedSupportSections_quasiIso : QuasiIso (relativeToClosedSupportSections O U) := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable ℚ X O U
  unfold relativeToClosedSupportSections
  infer_instance

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit.Constructions
