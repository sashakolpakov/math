import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportSheaf
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportThomResolution

/-! # Support Section Changes -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSectionChanges.Constructions

noncomputable section

/-! Actual changes of specified supports and open-set restrictions give natural section maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] {X : TopCat.{0}} {C D : Opens X} (h : C ≤ D)

def closedSupportChange (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf D F ⟶ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf C F :=
  kernel.lift _ (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion D F)
    (IntersectSupportSheaf.Constructions.sheafMorphism_restrict_zero_of_le h _ (kernel.condition _))

@[reassoc]
theorem closedSupportChange_inclusion (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    closedSupportChange h F ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C F = CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion D F :=
  kernel.lift_ι _ _ _

def closedSupportChangeNatTrans : ClosedSupportIs.Constructions.closedSupportSheafFunctor (R := R) D ⟶ ClosedSupportIs.Constructions.closedSupportSheafFunctor C where
  app := closedSupportChange h
  naturality F G f := by
    apply (cancel_mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C G)).mp
    change (ClosedSupportIs.Constructions.closedSupportSheafMap D f ≫ closedSupportChange h G) ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C G =
      (closedSupportChange h F ≫ ClosedSupportIs.Constructions.closedSupportSheafMap C f) ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C G
    rw [Category.assoc, closedSupportChange_inclusion, ClosedSupportIs.Constructions.closedSupportSheafMap_inclusion,
      Category.assoc, ClosedSupportIs.Constructions.closedSupportSheafMap_inclusion, ← Category.assoc, closedSupportChange_inclusion]

def closedSupportSectionChange (U : Opens X) :
    ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := R) D U ⟶ ClosedSupportIs.Constructions.closedSupportSectionFunctor C U :=
  Functor.whiskerRight (closedSupportChangeNatTrans h) (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U)

def closedSupportSectionRestriction (O : Opens X) {U W : Opens X} (i : U ⟶ W) :
    ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := R) O W ⟶ ClosedSupportIs.Constructions.closedSupportSectionFunctor O U where
  app F := (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O F).obj.map i.op
  naturality _F _G f := ((ClosedSupportIs.Constructions.closedSupportSheafMap O f).hom.naturality i.op).symm

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
variable (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

include ha in
theorem regularSourceThomClosedSupportIso_naturality
    (O U P W : Opens Z.regularAmbientSpace)
    (α : ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O U ⟶
      ClosedSupportIs.Constructions.closedSupportSectionFunctor P W) (n : ℕ) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
        (RegularThomSourceSheaf.Constructions.regularSourceSheafComplex Z)) n ≫ (ClosedSupportThomResolution.Constructions.regularSourceThomClosedSupportIso Z a ha P W n).hom =
      (ClosedSupportThomResolution.Constructions.regularSourceThomClosedSupportIso Z a ha O U n).hom ≫
        HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
          (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)) n :=
  ClosedSupportThomResolution.Constructions.closedSupportDerivedResolutionIso_functor_naturality (X := TopCat.of Z.regularAmbientSpace)
    O U P W α (RegularThomSourceSheaf.Constructions.regularSourceSheafComplex Z)
    (ClosedSourceResolution.Constructions.closedSourceSheaf_isFlasque (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)) (AllThomSource.Constructions.regularSourceSheaf_exact_positive Z)
    (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z) (ThomGoodShiftFlasque.Constructions.regularThomGoodShift_isFlasque Z)
    (AllThomSource.Constructions.regularThomGoodShift_exact_positive Z) (RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso Z a ha) n

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSectionChanges.Constructions
