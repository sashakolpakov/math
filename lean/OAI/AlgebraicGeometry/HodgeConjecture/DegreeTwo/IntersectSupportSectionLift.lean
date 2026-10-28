import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportInclusion

/-! # Intersect Support Section Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportSectionLift.Constructions

noncomputable section

/-! Two compatible supported cochain maps lift to the actual intersection-support section complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (C O U : Opens X)
variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)

def supportedSectionInclusion : CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K) ⟶
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U K :=
  ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C K)

instance supportedSectionInclusion_mono : Mono (supportedSectionInclusion C U K) := by
  unfold supportedSectionInclusion
  rw [← ClosedSupportIs.Constructions.closedSupportFunctorComplexIso_inclusion, Functor.map_comp]
  have hm : Mono (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (ClosedSupportIs.Constructions.closedSupportCochainInclusion C K)) := ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion_mono C U K
  infer_instance

theorem supportedSectionInclusion_restriction_zero :
    supportedSectionInclusion O U K ≫
        CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction K (homOfLE (inf_le_left : U ⊓ O ≤ U)) = 0 := by
  change ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O K) ≫ _ = 0
  rw [← ClosedSupportIs.Constructions.supportedSheafSectionsIsoKernel_inclusion, Category.assoc, kernel.condition, comp_zero]

variable {N : CochainComplex (ModuleCat.{0} ℚ) ℕ}
variable (fC : N ⟶ CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K))
variable (fO : N ⟶ CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O K))
variable (hf : fC ≫ supportedSectionInclusion C U K = fO ≫ supportedSectionInclusion O U K)

include hf in
theorem intersectSupportSectionLift_condition :
    fC ≫ CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K)
      (homOfLE (inf_le_left : U ⊓ O ≤ U)) = 0 := by
  apply (cancel_mono (supportedSectionInclusion C (U ⊓ O) K)).mp
  rw [zero_comp, Category.assoc]
  have hn : CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K)
      (homOfLE (inf_le_left : U ⊓ O ≤ U)) ≫ supportedSectionInclusion C (U ⊓ O) K =
    supportedSectionInclusion C U K ≫
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction K (homOfLE (inf_le_left : U ⊓ O ≤ U)) :=
    (ClosedSupportComparison.Constructions.moduleSheafSectionsRestriction_naturality (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C K)
      (homOfLE (inf_le_left : U ⊓ O ≤ U))).symm
  rw [hn, ← Category.assoc, hf, Category.assoc, supportedSectionInclusion_restriction_zero, comp_zero]

def intersectSupportSectionLift :
    N ⟶ GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K) :=
  kernel.lift _ fC (intersectSupportSectionLift_condition C O U K fC fO hf) ≫
    (ClosedSupportIs.Constructions.closedSupportSectionKernelIso O U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K)).inv

theorem intersectSupportSectionLift_left :
    intersectSupportSectionLift C O U K fC fO hf ≫
      ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion O U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K) = fC := by
  unfold intersectSupportSectionLift ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion
  rw [Category.assoc, ← ClosedSupportIs.Constructions.closedSupportSectionKernelIso_inclusion, Iso.inv_hom_id_assoc, kernel.lift_ι]

theorem intersectSupportSectionLift_inclusion :
    intersectSupportSectionLift C O U K fC fO hf ≫ IntersectSupportInclusion.Constructions.intersectSupportSectionInclusion C O K U =
      fC ≫ supportedSectionInclusion C U K := by
  change intersectSupportSectionLift C O U K fC fO hf ≫
    (ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion O U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K) ≫ supportedSectionInclusion C U K) = _
  rw [← Category.assoc, intersectSupportSectionLift_left]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportSectionLift.Constructions
