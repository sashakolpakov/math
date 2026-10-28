import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupSheaf
import OAI.AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison

/-! # Thom Cup Forget Unit -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ThomCupForgetUnit

noncomputable section

section

/-! The original relative Thom cocycle and global singular cochains give the actual global sheaf cup. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0}) (C : Opens X)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (C : Set X)) 2)

theorem relativeTwoCupSheafMap_global_unit :
    AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X ≫
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := X) ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupSheafMap X C a) =
      HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.relativeTwoCupCochainMap X (C : Set X) a ≫
        HomologicalComplex.restrictionMap
          (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) X C)
          (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2) := by
  change (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (Opens.inclusion' (⊤ : Opens X)) ≫
    AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X ⊤) ≫
      HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupSheafSectionsMap X C a ⊤ = _
  rw [Category.assoc, HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupSheafSectionsMap_unit, ← Category.assoc]
  have ht := HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.relativeTwoCupCochainMap_naturality X (C : Set X) a
    (Opens.inclusion' (⊤ : Opens X)) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (C : Set X) (⊤ : Opens X)) (fun _ hx => hx)
  change AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (Opens.inclusion' (⊤ : Opens X)) ≫
    HodgeConjecture.DegreeTwo.RelativeCupPresheaf.Constructions.relativeTwoCupOpenCochainMap X (C : Set X) a ⊤ = _ at ht
  rw [ht, Category.assoc, ← HomologicalComplex.restrictionMap_comp]
  rfl

end

/-! Forgetting the Thom support recovers the native cup cochain, including a relative right input. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0}) (C : Opens X)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (C : Set X)) 2)

theorem relativeTwoCupSheafMap_global_forget_value (n : ℕ)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion (ModuleCat.of ℚ ℚ) X C ⊤).f (2+n)
      ((HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupSheafSectionsMap X C a ⊤).f n
        ((AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X).f n b)) =
      (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X).f (2+n)
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (C : Set X)).f (2+n)
          (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X (C : Set X) 2 n a.val b)) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun g => g.f n) (relativeTwoCupSheafMap_global_unit X C a)) b
  change (HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupSheafSectionsMap X C a ⊤).f n
      ((AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X).f n b) =
    (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) X C).f (2+n)
      (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X (C : Set X) 2 n a.val b) at h
  rw [h]
  exact ConcreteCategory.congr_hom
    (congrArg (fun g => g.f (2+n))
      (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections_inclusion (ModuleCat.of ℚ ℚ) X C))
    (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X (C : Set X) 2 n a.val b)

theorem relativeTwoCupSheafMap_relative_input (O : Opens X) (n : ℕ)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)).X n) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion (ModuleCat.of ℚ ℚ) X C ⊤).f (2+n)
      ((HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupSheafSectionsMap X C a ⊤).f n
        ((AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X).f n
          ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (O : Set X)).f n b))) =
      (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X).f (2+n)
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (O : Set X)).f (2+n)
          (CycleClass.Geometric.RelativeCup.Cycles.absoluteRelativeCup X (O : Set X) 2 n
            ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (C : Set X)).f 2 a.val) b)) := by
  rw [relativeTwoCupSheafMap_global_forget_value]
  congr 1
  simp only [CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup, CycleClass.Geometric.RelativeCup.Cycles.absoluteRelativeCup,
    CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_inclusion, CycleClass.Geometric.RelativeCup.Cycles.absoluteRelativeCupWith_inclusion]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ThomCupForgetUnit
