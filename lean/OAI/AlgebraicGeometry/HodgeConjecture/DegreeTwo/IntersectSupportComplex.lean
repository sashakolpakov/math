import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportSheaf
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportIs

/-! # Intersect Support Complex -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportComplex.Constructions

noncomputable section

/-! The intersection-support identification acts on the original cochain complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] {X : TopCat.{0}} (C O : Opens X)

theorem intersectSupportInclusion_naturality
    {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (f : F ⟶ G) :
    ClosedSupportIs.Constructions.closedSupportSheafMap O (ClosedSupportIs.Constructions.closedSupportSheafMap C f) ≫ IntersectSupportSheaf.Constructions.intersectSupportInclusion C O G =
      IntersectSupportSheaf.Constructions.intersectSupportInclusion C O F ≫ f := by
  unfold IntersectSupportSheaf.Constructions.intersectSupportInclusion
  rw [← Category.assoc, ClosedSupportIs.Constructions.closedSupportSheafMap_inclusion, Category.assoc,
    ClosedSupportIs.Constructions.closedSupportSheafMap_inclusion, ← Category.assoc]

theorem intersectSupportSheafIso_naturality
    {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (f : F ⟶ G) :
    ClosedSupportIs.Constructions.closedSupportSheafMap O (ClosedSupportIs.Constructions.closedSupportSheafMap C f) ≫ (IntersectSupportSheaf.Constructions.intersectSupportSheafIso C O G).hom =
      (IntersectSupportSheaf.Constructions.intersectSupportSheafIso C O F).hom ≫ ClosedSupportIs.Constructions.closedSupportSheafMap (C ⊔ O) f := by
  apply (cancel_mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion (C ⊔ O) G)).mp
  change (ClosedSupportIs.Constructions.closedSupportSheafMap O (ClosedSupportIs.Constructions.closedSupportSheafMap C f) ≫ IntersectSupportSheaf.Constructions.intersectSupportToUnion C O G) ≫
      CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion (C ⊔ O) G =
    (IntersectSupportSheaf.Constructions.intersectSupportToUnion C O F ≫ ClosedSupportIs.Constructions.closedSupportSheafMap (C ⊔ O) f) ≫
      CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion (C ⊔ O) G
  rw [Category.assoc, IntersectSupportSheaf.Constructions.intersectSupportToUnion_inclusion, Category.assoc,
    ClosedSupportIs.Constructions.closedSupportSheafMap_inclusion, ← Category.assoc, IntersectSupportSheaf.Constructions.intersectSupportToUnion_inclusion,
    intersectSupportInclusion_naturality]

def intersectSupportFunctorIso :
    ClosedSupportIs.Constructions.closedSupportSheafFunctor (R := R) C ⋙ ClosedSupportIs.Constructions.closedSupportSheafFunctor O ≅
      ClosedSupportIs.Constructions.closedSupportSheafFunctor (C ⊔ O) :=
  NatIso.ofComponents (IntersectSupportSheaf.Constructions.intersectSupportSheafIso C O)
    (fun f => intersectSupportSheafIso_naturality C O f)

def intersectSupportFunctorComplexIso
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    ((ClosedSupportIs.Constructions.closedSupportSheafFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (((ClosedSupportIs.Constructions.closedSupportSheafFunctor C).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ≅
      ((ClosedSupportIs.Constructions.closedSupportSheafFunctor (C ⊔ O)).mapHomologicalComplex (ComplexShape.up ℕ)).obj K := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => IntersectSupportSheaf.Constructions.intersectSupportSheafIso C O (K.X n)) ?_
  intro i j hij
  exact (intersectSupportSheafIso_naturality C O (K.d i j)).symm

def intersectSupportedComplexIso
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    ((ClosedSupportIs.Constructions.closedSupportSheafFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K) ≅ CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex (C ⊔ O) K :=
  ((ClosedSupportIs.Constructions.closedSupportSheafFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
      (ClosedSupportIs.Constructions.closedSupportFunctorComplexIso C K) ≪≫
    intersectSupportFunctorComplexIso C O K ≪≫ (ClosedSupportIs.Constructions.closedSupportFunctorComplexIso (C ⊔ O) K).symm

def intersectSupportedSectionsIso (U : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    ((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K) ≅
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex (C ⊔ O) K) :=
  ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
    (intersectSupportedComplexIso C O K)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportComplex.Constructions
