import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularSheafPullback
import OAI.AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison

/-! # Source Cohomology -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SourceCohomology

noncomputable section

section

/-!
Closed supports commute with the actual source sheaf pushforward. The
comparison is induced by the original restriction maps and retains their
kernel inclusions, in every cochain degree.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R] {X Y : TopCat.{0}} (f : Y ⟶ X) (O : Opens X)
variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) Y) ℕ)

abbrev sourcePushforwardComplex :=
  ((TopCat.Sheaf.pushforward (ModuleCat.{0} R) f).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K

theorem sourcePushforwardRestriction :
    ((TopCat.Sheaf.pushforward (ModuleCat.{0} R) f).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (CycleClass.Geometric.SupportStalkVanishes.Cohomology.sheafRestrictionComplex ((Opens.map f).obj O) K) =
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.sheafRestrictionComplex O (sourcePushforwardComplex f K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rfl

def supportedSourcePushforwardIso :
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O (sourcePushforwardComplex f K) ≅
      sourcePushforwardComplex f (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex ((Opens.map f).obj O) K) :=
  kernelIsoOfEq (sourcePushforwardRestriction f O K).symm ≪≫
    (PreservesKernel.iso
      ((TopCat.Sheaf.pushforward (ModuleCat.{0} R) f).mapHomologicalComplex
        (ComplexShape.up ℕ))
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.sheafRestrictionComplex ((Opens.map f).obj O) K)).symm

theorem supportedSourcePushforwardIso_inclusion :
    (supportedSourcePushforwardIso f O K).hom ≫
      ((TopCat.Sheaf.pushforward (ModuleCat.{0} R) f).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion ((Opens.map f).obj O) K) =
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O (sourcePushforwardComplex f K) := by
  unfold supportedSourcePushforwardIso
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  simp only [CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion, PreservesKernel.iso_inv_ι,
    kernelIsoOfEq_hom_comp_ι]

end

/-! Source sections with prescribed support compute the original relative singular cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R] (M : ModuleCat.{0} R)
variable {X Y : TopCat.{0}} (f : Y ⟶ X) (O U : Opens X)

def supportedSourceSectionsIso :
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularPushforwardSheafComplex M f)) ≅
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSections M Y ((Opens.map f).obj O) ((Opens.map f).obj U) :=
  ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
    (supportedSourcePushforwardIso f O (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M Y)))

def relativeToSupportedSourceGlobalSections :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M Y (((Opens.map f).obj O) : Set Y) ⟶
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex ⊤
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularPushforwardSheafComplex M f)) :=
  AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections M Y ((Opens.map f).obj O) ≫
    (supportedSourceSectionsIso M f O ⊤).inv

theorem relativeToSupportedSourceGlobalSections_inclusion :
    relativeToSupportedSourceGlobalSections M f O ≫
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := R) (⊤ : Opens X)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularPushforwardSheafComplex M f)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M Y (((Opens.map f).obj O) : Set Y) ≫
      AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections M Y := by
  have hi := congrArg
    (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := R) (⊤ : Opens X)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map)
    (supportedSourcePushforwardIso_inclusion f O
      (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M Y)))
  rw [Functor.map_comp] at hi
  change (supportedSourceSectionsIso M f O ⊤).hom ≫
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion M Y ((Opens.map f).obj O) ⊤ = _ at hi
  unfold relativeToSupportedSourceGlobalSections
  erw [Category.assoc, ← hi, Iso.inv_hom_id_assoc]
  exact AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections_inclusion M Y ((Opens.map f).obj O)

variable [MetrizableSpace Y]

theorem relativeToSupportedSourceGlobalSections_quasiIso :
    QuasiIso (relativeToSupportedSourceGlobalSections (ModuleCat.of ℚ ℚ) f O) := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafGlobalSections_of_metrizable ℚ Y ((Opens.map f).obj O)
  unfold relativeToSupportedSourceGlobalSections
  infer_instance

def supportedSourceGlobalCohomologyIso (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex ⊤
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f))).homology n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y (((Opens.map f).obj O) : Set Y) n := by
  have := relativeToSupportedSourceGlobalSections_quasiIso f O
  exact (isoOfQuasiIsoAt (relativeToSupportedSourceGlobalSections (ModuleCat.of ℚ ℚ) f O) n).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SourceCohomology
