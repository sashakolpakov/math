import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AllThomSource
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DerivedResolutionComparison

/-! # Closed Support Is -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions

noncomputable section

section

/-! The all-degree source–Thom isomorphism intertwines genuine pullback with the original normalized cup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

theorem regularAmbientSingularSheaf_exact_positive (n : ℕ) :
    (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex (TopCat.of Z.regularAmbientSpace)).ExactAt (n+1) := by
  have := AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace V.analyticModel Z.regularAmbientSpace
  exact SingularSheafZeroResolution.Constructions.rationalSingularSheaf_positive_exact (TopCat.of Z.regularAmbientSpace) n

theorem regularAmbientSingularSheaf_isFlasque (n : ℕ) :
    TopCat.Sheaf.IsFlasque ((SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex (TopCat.of Z.regularAmbientSpace)).X n) :=
  AlgebraicTopology.Cohomology.Singular.SheafFlasque.sheafifiedSingularCochains_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ)
    (TopCat.of Z.regularAmbientSpace) n

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceThomAllDegreeSectionsIso_comm (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) U).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
          (SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (RegularTopGysin.Constructions.regularSourceInclusionMap V Z))) n ≫
        (AllThomSource.Constructions.regularSourceThomAllDegreeSectionsIso Z a ha U n).hom =
      HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) U).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
          (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap (TopCat.of Z.regularAmbientSpace)
            Z.regularThomComplementOpen a)) n :=
  DerivedResolutionComparison.Constructions.derivedResolutionSectionIso_comm (RegularThomSourceSheaf.Constructions.regularSourceSheafComplex Z) (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)
    (ClosedSourceResolution.Constructions.closedSourceSheaf_isFlasque (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)) (AllThomSource.Constructions.regularSourceSheaf_exact_positive Z)
    (ThomGoodShiftFlasque.Constructions.regularThomGoodShift_isFlasque Z) (AllThomSource.Constructions.regularThomGoodShift_exact_positive Z)
    (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex (TopCat.of Z.regularAmbientSpace))
    (regularAmbientSingularSheaf_isFlasque Z) (regularAmbientSingularSheaf_exact_positive Z)
    (SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (RegularTopGysin.Constructions.regularSourceInclusionMap V Z))
    (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen a)
    (RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso Z a ha) (RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso_comm Z a ha) U n

theorem regularSourceThomAllDegreeRelativeIso_cup (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (SingularSheafPullback.Constructions.openPreimageMap (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U) n ≫
        (AllThomSource.Constructions.regularSourceThomAllDegreeRelativeIso Z a ha U n).hom =
      ModuleCat.ofHom (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U) 2 n
        (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U 2 Z.regularThomClass)) := by
  rw [← ClosedSourceResolution.Constructions.rationalSourceSheafPullback_sections_cohomology (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U n]
  simp only [AllThomSource.Constructions.regularSourceThomAllDegreeRelativeIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc
    (HomologicalComplex.homologyMap
      (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) U).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
        (SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (RegularTopGysin.Constructions.regularSourceInclusionMap V Z))) n),
    regularSourceThomAllDegreeSectionsIso_comm]
  rw [ThomSource.Constructions.regularThomSectionsRelativeIso_eq]
  have h := SupportedCupSectionCohomology.Constructions.relativeTwoCupGoodShiftSheafSections_cohomology
    (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen a
    (fun i hi => RegularThomSheafPurity.Constructions.regularThomSheaf_exactAt_except Z i (by omega)) U n
  rw [RelativeCupShiftSections.Constructions.relativeTwoCocycleOpenRestriction_class, ha] at h
  exact h

end

section

/-! The genuine closed-support kernel is an additive functor on sheaves and their cochain complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] {X : TopCat.{0}} (O : Opens X)

instance closedSupportSheafInclusion_mono (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    Mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O F) := inferInstanceAs (Mono (kernel.ι (CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen O F)))

def closedSupportSheafMap {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (f : F ⟶ G) :
    CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O F ⟶ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O G :=
  kernel.map (CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen O F) (CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpen O G) f
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.openRestrictionPushforwardFunctor O).map f) ((CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpenNatTrans O).naturality f).symm

@[reassoc]
theorem closedSupportSheafMap_inclusion {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (f : F ⟶ G) :
    closedSupportSheafMap O f ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O G =
      CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O F ≫ f :=
  kernel.lift_ι _ _ _

def closedSupportSheafFunctor : TopCat.Sheaf (ModuleCat.{0} R) X ⥤ TopCat.Sheaf (ModuleCat.{0} R) X where
  obj F := CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O F
  map f := closedSupportSheafMap O f
  map_id F := by
    apply (cancel_mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O F)).mp
    rw [closedSupportSheafMap_inclusion, Category.comp_id, Category.id_comp]
  map_comp f g := by
    apply (cancel_mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O _)).mp
    simp only [closedSupportSheafMap_inclusion_assoc, closedSupportSheafMap_inclusion, Category.assoc]

instance closedSupportSheafFunctor_additive : (closedSupportSheafFunctor (R := R) O).Additive where
  map_add {F G} {f g} := by
    apply (cancel_mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O _)).mp
    change closedSupportSheafMap O (f+g) ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O G =
      (closedSupportSheafMap O f + closedSupportSheafMap O g) ≫ CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O G
    rw [closedSupportSheafMap_inclusion, add_comp, closedSupportSheafMap_inclusion,
      closedSupportSheafMap_inclusion, comp_add]

def closedSupportFunctorComplexIso
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O K ≅
      ((closedSupportSheafFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).obj K := by
  refine HomologicalComplex.Hom.isoOfComponents (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso O K) ?_
  intro i j hij
  apply (cancel_mono (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X j))).mp
  change ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso O K i).hom ≫ closedSupportSheafMap O (K.d i j)) ≫
    CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X j) =
      ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O K).d i j ≫ (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso O K j).hom) ≫
        CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X j)
  rw [Category.assoc, closedSupportSheafMap_inclusion, ← Category.assoc,
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso_inclusion, Category.assoc,
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso_inclusion]
  exact (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O K).comm i j

def closedSupportSectionFunctor (U : Opens X) : TopCat.Sheaf (ModuleCat.{0} R) X ⥤ ModuleCat.{0} R :=
  closedSupportSheafFunctor O ⋙ CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U

instance closedSupportSectionFunctor_additive (U : Opens X) :
    (closedSupportSectionFunctor (R := R) O U).Additive := by
  change (closedSupportSheafFunctor (R := R) O ⋙ CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).Additive
  infer_instance

end

section

/-! Actual sections of the closed-support functor are the original restriction kernel complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] {X : TopCat.{0}} (O : Opens X)

def closedSupportCochainInclusion
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    ((closedSupportSheafFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ K where
  f n := CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X n)
  comm' i j _hij := (closedSupportSheafMap_inclusion O (K.d i j)).symm

theorem closedSupportFunctorComplexIso_inclusion
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    (closedSupportFunctorComplexIso O K).hom ≫ closedSupportCochainInclusion O K =
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O K := by
  ext n : 1
  exact CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso_inclusion O K n

theorem closedSupportFunctorComplexIso_inv_inclusion
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    (closedSupportFunctorComplexIso O K).inv ≫ CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O K =
      closedSupportCochainInclusion O K := by
  apply (cancel_epi (closedSupportFunctorComplexIso O K).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, closedSupportFunctorComplexIso_inclusion]

def closedSupportSectionKernelIso (U : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    ((closedSupportSectionFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ≅
      kernel (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction K (homOfLE (inf_le_left : U ⊓ O ≤ U))) :=
  ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
      (closedSupportFunctorComplexIso O K).symm ≪≫ CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafSectionsIsoKernel O U K

theorem supportedSheafSectionsIsoKernel_inclusion (U : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafSectionsIsoKernel O U K).hom ≫
        kernel.ι (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction K (homOfLE (inf_le_left : U ⊓ O ≤ U))) =
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O K) := by
  change (PreservesKernel.iso ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ))
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.sheafRestrictionComplex O K)).hom ≫ kernel.ι
      (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.sheafRestrictionComplex O K)) = _
  rw [PreservesKernel.iso_hom]
  exact kernelComparison_comp_ι (CycleClass.Geometric.SupportStalkVanishes.Cohomology.sheafRestrictionComplex O K)
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ))

theorem closedSupportSectionKernelIso_inclusion (U : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    (closedSupportSectionKernelIso O U K).hom ≫
        kernel.ι (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction K (homOfLE (inf_le_left : U ⊓ O ≤ U))) =
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (closedSupportCochainInclusion O K) := by
  simp only [closedSupportSectionKernelIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc]
  rw [supportedSheafSectionsIsoKernel_inclusion, ← Functor.map_comp,
    closedSupportFunctorComplexIso_inv_inclusion]

end

/-! Specified ambient support on the independent source resolution computes the actual source relative cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (O U : Opens X)

def closedSourceSupportedSectionsIso :
    ((closedSupportSectionFunctor (R := ℚ) O U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f) ≅
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSections (ModuleCat.of ℚ ℚ) Y
        ((Opens.map f).obj O) ((Opens.map f).obj U) :=
  closedSupportSectionKernelIso O U (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f) ≪≫
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafSectionsIsoKernel ((Opens.map f).obj O) ((Opens.map f).obj U)
      (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex Y)).symm

variable [MetrizableSpace Y]

def closedSourceSupportedRelativeCohomologyIso (n : ℕ) :
    (((closedSupportSectionFunctor (R := ℚ) O U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f)).homology n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of ((Opens.map f).obj U))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := Y) (((Opens.map f).obj O : Opens Y) : Set Y)
        ((Opens.map f).obj U)) n := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable ℚ Y
    ((Opens.map f).obj O) ((Opens.map f).obj U)
  exact (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) n).mapIso
      (closedSourceSupportedSectionsIso f O U) ≪≫
    (isoOfQuasiIsoAt (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) Y
      ((Opens.map f).obj O) ((Opens.map f).obj U)) n).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions
