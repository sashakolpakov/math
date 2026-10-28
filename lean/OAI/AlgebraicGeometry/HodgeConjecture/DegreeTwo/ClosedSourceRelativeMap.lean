import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportIs
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSectionChanges

/-! # Closed Source Relative Map -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap.Constructions

noncomputable section

section

/-! The source-relative comparison retains its actual cochain inclusion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (O U : Opens X)

def closedSupportSectionInclusion
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ) :
    GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) K ⟶ CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U K :=
  ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (ClosedSupportIs.Constructions.closedSupportCochainInclusion O K)

instance closedSupportSectionInclusion_mono
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ) :
    Mono (closedSupportSectionInclusion O U K) :=
  HomologicalComplex.mono_of_mono_f _ (fun n => by
    change Mono ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X n)))
    infer_instance)

theorem closedSupportSectionChange_inclusion {C D : Opens X} (h : C ≤ D)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ) :
    (NatTrans.mapHomologicalComplex (SupportSectionChanges.Constructions.closedSupportSectionChange h U) (ComplexShape.up ℕ)).app K ≫
        closedSupportSectionInclusion C U K = closedSupportSectionInclusion D U K := by
  ext n : 1
  change (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map (SupportSectionChanges.Constructions.closedSupportChange h (K.X n)) ≫
      (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion C (K.X n)) =
    (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion D (K.X n))
  rw [← Functor.map_comp, SupportSectionChanges.Constructions.closedSupportChange_inclusion]

variable {Y : TopCat.{0}} (f : Y ⟶ X)

theorem closedSourceSupportedSectionsIso_inclusion :
    (ClosedSupportIs.Constructions.closedSourceSupportedSectionsIso f O U).hom ≫
        CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion (ModuleCat.of ℚ ℚ) Y
          ((Opens.map f).obj O) ((Opens.map f).obj U) =
      closedSupportSectionInclusion O U (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f) := by
  unfold ClosedSupportIs.Constructions.closedSourceSupportedSectionsIso
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have hi := ClosedSupportIs.Constructions.supportedSheafSectionsIsoKernel_inclusion ((Opens.map f).obj O)
    ((Opens.map f).obj U) (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex Y)
  change (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafSectionsIsoKernel ((Opens.map f).obj O)
    ((Opens.map f).obj U) (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex Y)).hom ≫
    kernel.ι (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex Y)
      (homOfLE (inf_le_left : (Opens.map f).obj U ⊓ (Opens.map f).obj O ≤ (Opens.map f).obj U))) =
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion (ModuleCat.of ℚ ℚ) Y
      ((Opens.map f).obj O) ((Opens.map f).obj U) at hi
  have hi' : (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafSectionsIsoKernel ((Opens.map f).obj O)
      ((Opens.map f).obj U) (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex Y)).inv ≫
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion (ModuleCat.of ℚ ℚ) Y
        ((Opens.map f).obj O) ((Opens.map f).obj U) =
    kernel.ι (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex Y)
      (homOfLE (inf_le_left : (Opens.map f).obj U ⊓ (Opens.map f).obj O ≤ (Opens.map f).obj U))) := by
    rw [← hi, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hi']
  exact ClosedSupportIs.Constructions.closedSupportSectionKernelIso_inclusion O U _

def closedSourceRelativeToSupportedSections :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of ((Opens.map f).obj U))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := Y) (((Opens.map f).obj O : Opens Y) : Set Y) ((Opens.map f).obj U)) ⟶
    GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U)
      (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f) :=
  AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) Y ((Opens.map f).obj O) ((Opens.map f).obj U) ≫
    (ClosedSupportIs.Constructions.closedSourceSupportedSectionsIso f O U).inv

theorem closedSourceRelativeToSupportedSections_inclusion :
    closedSourceRelativeToSupportedSections O U f ≫
      closedSupportSectionInclusion O U (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of ((Opens.map f).obj U))
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := Y) (((Opens.map f).obj O : Opens Y) : Set Y) ((Opens.map f).obj U)) ≫
      AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) Y ((Opens.map f).obj U) := by
  unfold closedSourceRelativeToSupportedSections
  rw [Category.assoc, ← closedSourceSupportedSectionsIso_inclusion O U f,
    Iso.inv_hom_id_assoc, AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections_inclusion]

variable [MetrizableSpace Y]

instance closedSourceRelativeToSupportedSections_quasiIso :
    QuasiIso (closedSourceRelativeToSupportedSections O U f) := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable ℚ Y
    ((Opens.map f).obj O) ((Opens.map f).obj U)
  unfold closedSourceRelativeToSupportedSections
  infer_instance

theorem closedSourceRelativeToSupportedSections_homology (n : ℕ) :
    HomologicalComplex.homologyMap (closedSourceRelativeToSupportedSections O U f) n ≫
      (ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso f O U n).hom = 𝟙 _ := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable ℚ Y
    ((Opens.map f).obj O) ((Opens.map f).obj U)
  change HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) Y
    ((Opens.map f).obj O) ((Opens.map f).obj U) ≫ (ClosedSupportIs.Constructions.closedSourceSupportedSectionsIso f O U).inv) n ≫
    (HomologicalComplex.homologyMap (ClosedSupportIs.Constructions.closedSourceSupportedSectionsIso f O U).hom n ≫
      (isoOfQuasiIsoAt (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) Y
        ((Opens.map f).obj O) ((Opens.map f).obj U)) n).inv) = 𝟙 _
  rw [HomologicalComplex.homologyMap_comp, Category.assoc, ← Category.assoc
    (HomologicalComplex.homologyMap (ClosedSupportIs.Constructions.closedSourceSupportedSectionsIso f O U).inv n),
    ← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id, HomologicalComplex.homologyMap_id,
    Category.id_comp]
  exact (isoOfQuasiIsoAt (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) Y
    ((Opens.map f).obj O) ((Opens.map f).obj U)) n).hom_inv_id

end

/-! The source-relative identification respects the original relative support-change maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {C D : Opens X} (h : C ≤ D) (U : Opens X)

def closedSourceRelativeSupportChange :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of ((Opens.map f).obj U))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := Y) (((Opens.map f).obj D : Opens Y) : Set Y) ((Opens.map f).obj U)) ⟶
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of ((Opens.map f).obj U))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := Y) (((Opens.map f).obj C : Opens Y) : Set Y) ((Opens.map f).obj U)) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) (𝟙 _) (fun _ hx => h hx)

theorem closedSourceRelativeSupportChange_inclusion :
    closedSourceRelativeSupportChange f h U ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of ((Opens.map f).obj U))
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := Y) (((Opens.map f).obj C : Opens Y) : Set Y) ((Opens.map f).obj U)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of ((Opens.map f).obj U))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := Y) (((Opens.map f).obj D : Opens Y) : Set Y) ((Opens.map f).obj U)) := by
  unfold closedSourceRelativeSupportChange
  rw [AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality, AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_id, Category.comp_id]

theorem closedSourceRelativeToSupportedSections_support_naturality :
    closedSourceRelativeSupportChange f h U ≫ closedSourceRelativeToSupportedSections C U f =
      closedSourceRelativeToSupportedSections D U f ≫
        (NatTrans.mapHomologicalComplex (SupportSectionChanges.Constructions.closedSupportSectionChange h U) (ComplexShape.up ℕ)).app
          (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f) := by
  apply (cancel_mono (closedSupportSectionInclusion C U
    (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f))).mp
  rw [Category.assoc, closedSourceRelativeToSupportedSections_inclusion,
    ← Category.assoc, closedSourceRelativeSupportChange_inclusion,
    Category.assoc, closedSupportSectionChange_inclusion,
    closedSourceRelativeToSupportedSections_inclusion]

variable [MetrizableSpace Y]

theorem closedSourceSupportedRelativeCohomologyIso_support_naturality (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (SupportSectionChanges.Constructions.closedSupportSectionChange h U) (ComplexShape.up ℕ)).app
          (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f)) n ≫
        (ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso f C U n).hom =
      (ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso f D U n).hom ≫
        HomologicalComplex.homologyMap (closedSourceRelativeSupportChange f h U) n := by
  apply (cancel_epi (HomologicalComplex.homologyMap (closedSourceRelativeToSupportedSections D U f) n)).mp
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    ← closedSourceRelativeToSupportedSections_support_naturality,
    HomologicalComplex.homologyMap_comp, Category.assoc,
    closedSourceRelativeToSupportedSections_homology, Category.comp_id,
    ← Category.assoc, closedSourceRelativeToSupportedSections_homology, Category.id_comp]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap.Constructions
