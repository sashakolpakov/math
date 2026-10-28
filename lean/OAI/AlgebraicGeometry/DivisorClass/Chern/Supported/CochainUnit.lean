import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SectionsLeftExact
import OAI.AlgebraicGeometry.DivisorClass.Chern.ThomCupForgetUnit

/-! # Cochain Unit -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.CochainUnit

noncomputable section

section

/-! The native relative cochain comparison retains its original inclusion after passing to the supported-section functor. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} (O U : Opens X)

def supportedSectionsCochainInclusion
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ) :
    HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex (DerivedComparison.supportedSectionsFunctor O U) K ⟶ CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U K where
  f n := SectionsLeftExact.supportedSectionsInclusion O U (K.X n)
  comm' i j _ := (SectionsLeftExact.supportedSectionsInclusion_naturality O U (K.d i j)).symm

instance supportedSectionsCochainInclusion_mono
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ) :
    Mono (supportedSectionsCochainInclusion O U K) :=
  HomologicalComplex.mono_of_mono_f _ (fun n => SectionsLeftExact.supportedSectionsInclusion_mono O U (K.X n))

theorem supportedSectionsCochainInclusion_naturality
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ} (f : K ⟶ L) :
    ((DerivedComparison.supportedSectionsFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).map f ≫
      supportedSectionsCochainInclusion O U L =
    supportedSectionsCochainInclusion O U K ≫
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact SectionsLeftExact.supportedSectionsInclusion_naturality O U (f.f n)

theorem supportedSectionsFunctorIso_inclusion
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ) :
    (DerivedComparison.supportedSectionsFunctorIso O U K).hom ≫ supportedSectionsCochainInclusion O U K =
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact congrArg ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).map)
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexDegreeIso_inclusion O K n)

def relativeToSupportedFunctorGlobalSections :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X) ⟶
      HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex (DerivedComparison.supportedSectionsFunctor O ⊤) (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) :=
  AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) X O ≫
    (DerivedComparison.supportedSectionsFunctorIso O ⊤ (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).hom

theorem relativeToSupportedFunctorGlobalSections_inclusion :
    relativeToSupportedFunctorGlobalSections O ≫
      supportedSectionsCochainInclusion O ⊤ (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (O : Set X) ≫
      AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X := by
  unfold relativeToSupportedFunctorGlobalSections
  rw [Category.assoc, supportedSectionsFunctorIso_inclusion]
  exact AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections_inclusion (ModuleCat.of ℚ ℚ) X O

theorem relativeToSupportedFunctorGlobalSections_inclusion_value (n : ℕ)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)).X n) :
    SectionsLeftExact.supportedSectionsInclusion O ⊤ ((HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X).X n)
      ((relativeToSupportedFunctorGlobalSections O).f n b) =
    (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X).f n
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (O : Set X)).f n b) :=
  ConcreteCategory.congr_hom
    (congrArg (fun g => g.f n) (relativeToSupportedFunctorGlobalSections_inclusion O)) b

end

/-! The supported sheaf cup retains exactly the native relative right-hand cup cochain. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem supportedSectionsInclusion_map_apply {X : TopCat.{0}} (O U : Opens X)
    {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (f : F ⟶ G)
    (s : (DerivedComparison.supportedSectionsFunctor O U).obj F) :
    SectionsLeftExact.supportedSectionsInclusion O U G ((DerivedComparison.supportedSectionsFunctor O U).map f s) =
      (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map f (SectionsLeftExact.supportedSectionsInclusion O U F s) :=
  ConcreteCategory.congr_hom (SectionsLeftExact.supportedSectionsInclusion_naturality O U f) s

variable (X : TopCat.{0}) (C O : Opens X)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (C : Set X)) 2)

theorem supportedRelativeTwoCup_forget_value (n : ℕ)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)).X n) :
    (DerivedComparison.supportedSectionsFunctor O ⊤).map
      ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).f (2+n))
      ((DerivedComparison.supportedSectionsFunctor O ⊤).map ((HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupSheafMap X C a).f n)
        ((relativeToSupportedFunctorGlobalSections O).f n b)) =
    (relativeToSupportedFunctorGlobalSections O).f (2+n)
      (CycleClass.Geometric.RelativeCup.Cycles.absoluteRelativeCup X (O : Set X) 2 n
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (C : Set X)).f 2 a.val) b) := by
  apply (ModuleCat.mono_iff_injective
    (SectionsLeftExact.supportedSectionsInclusion O ⊤ ((HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X).X (2+n)))).mp inferInstance
  erw [supportedSectionsInclusion_map_apply, supportedSectionsInclusion_map_apply,
    relativeToSupportedFunctorGlobalSections_inclusion_value,
    relativeToSupportedFunctorGlobalSections_inclusion_value]
  exact ThomCupForgetUnit.relativeTwoCupSheafMap_relative_input X C a O n b

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.CochainUnit
