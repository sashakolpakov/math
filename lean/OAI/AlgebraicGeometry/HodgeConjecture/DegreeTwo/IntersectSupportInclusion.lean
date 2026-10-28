import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportComplex
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap

/-! # Intersect Support Inclusion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportInclusion.Constructions

noncomputable section

/-! The intersection-support complex isomorphism retains the actual inclusion into ambient cochains. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (C O : Opens X)
variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)

theorem intersectSupportFunctorComplexIso_inclusion :
    (IntersectSupportComplex.Constructions.intersectSupportFunctorComplexIso C O K).hom ≫ ClosedSupportIs.Constructions.closedSupportCochainInclusion (C ⊔ O) K =
      ClosedSupportIs.Constructions.closedSupportCochainInclusion O
        (((ClosedSupportIs.Constructions.closedSupportSheafFunctor C).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ≫
        ClosedSupportIs.Constructions.closedSupportCochainInclusion C K := by
  ext n : 1
  exact IntersectSupportSheaf.Constructions.intersectSupportToUnion_inclusion C O (K.X n)

theorem intersectSupportedComplexIso_inclusion :
    (IntersectSupportComplex.Constructions.intersectSupportedComplexIso C O K).hom ≫ CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion (C ⊔ O) K =
      ClosedSupportIs.Constructions.closedSupportCochainInclusion O (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K) ≫ CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C K := by
  simp only [IntersectSupportComplex.Constructions.intersectSupportedComplexIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc]
  rw [ClosedSupportIs.Constructions.closedSupportFunctorComplexIso_inv_inclusion,
    intersectSupportFunctorComplexIso_inclusion, ← Category.assoc,
    ClosedSupportComparison.Constructions.closedSupportCochainInclusion_naturality, Category.assoc,
    ClosedSupportIs.Constructions.closedSupportFunctorComplexIso_inclusion]

def intersectSupportSectionInclusion (U : Opens X) :
    GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K) ⟶
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U K :=
  ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion O U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K) ≫
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C K)

theorem intersectSupportedSectionsIso_inclusion (U : Opens X) :
    (IntersectSupportComplex.Constructions.intersectSupportedSectionsIso C O U K).hom ≫
        ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion (C ⊔ O) K) = intersectSupportSectionInclusion C O K U := by
  change ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (IntersectSupportComplex.Constructions.intersectSupportedComplexIso C O K).hom ≫
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion (C ⊔ O) K) = _
  rw [← Functor.map_comp, intersectSupportedComplexIso_inclusion, Functor.map_comp]
  rfl

instance intersectSupportSectionInclusion_mono (U : Opens X) :
    Mono (intersectSupportSectionInclusion C O K U) := by
  have h : Mono (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion (C ⊔ O) K)) := by
    rw [← ClosedSupportIs.Constructions.closedSupportFunctorComplexIso_inclusion, Functor.map_comp]
    have hm : Mono (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (ClosedSupportIs.Constructions.closedSupportCochainInclusion (C ⊔ O) K)) :=
      ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion_mono (C ⊔ O) U K
    infer_instance
  rw [← intersectSupportedSectionsIso_inclusion]
  infer_instance

theorem intersectSupportSectionChange_inclusion {D : Opens X} (h : O ≤ D) (U : Opens X) :
    (NatTrans.mapHomologicalComplex (SupportSectionChanges.Constructions.closedSupportSectionChange h U) (ComplexShape.up ℕ)).app
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K) ≫ intersectSupportSectionInclusion C O K U =
      intersectSupportSectionInclusion C D K U := by
  unfold intersectSupportSectionInclusion
  rw [← Category.assoc, ClosedSourceRelativeMap.Constructions.closedSupportSectionChange_inclusion]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportInclusion.Constructions
