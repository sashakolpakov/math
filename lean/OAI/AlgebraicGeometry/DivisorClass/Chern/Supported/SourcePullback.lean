import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SourceCohomology
import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SectionQuasiIso

/-! # Source Pullback -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SourcePullback

noncomputable section

/-! The actual supported source sheaf map induces the original relative singular pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R] (M : ModuleCat.{0} R)
variable {X Y : TopCat.{0}} (f : Y ⟶ X) (O : Opens X)

theorem singularSheafPullback_global_unit :
    AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections M X ≫
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := R) (⊤ : Opens X)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularSheafPullbackMap M f) =
    AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M f ≫ AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections M Y := by
  have h : AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections M X ⊤ ≫
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := R) (⊤ : Opens X)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularSheafPullbackMap M f) =
    AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap f ⊤) ≫
      AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections M Y ((Opens.map f).obj ⊤) := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularSheafPullbackMap_unit M f ⊤ n
  change (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (Opens.inclusion' (⊤ : Opens X)) ≫
    AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections M X ⊤) ≫ _ =
    AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M f ≫ (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (Opens.inclusion' (⊤ : Opens Y)) ≫
      AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections M Y ⊤)
  rw [Category.assoc, h, ← Category.assoc, ← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp,
    ← Category.assoc, ← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp]
  rfl

def supportedSourcePullback :
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O ⟶
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularPushforwardSheafComplex M f) :=
  SectionQuasiIso.supportedSheafComplexMap O (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularSheafPullbackMap M f)

theorem relativeToSupportedSourceGlobalSections_pullback :
    AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections M X O ≫
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := R) (⊤ : Opens X)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (supportedSourcePullback M f O) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f
        (A := (((Opens.map f).obj O) : Set Y)) (B := (O : Set X)) (fun _ hy => hy) ≫
      SourceCohomology.relativeToSupportedSourceGlobalSections M f O := by
  let F := (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := R) (⊤ : Opens X)).mapHomologicalComplex (ComplexShape.up ℕ)
  let i := CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularPushforwardSheafComplex M f)
  have : Mono (F.map i) := by
    dsimp [i, F]
    infer_instance
  apply (cancel_mono (F.map i)).mp
  rw [Category.assoc, Category.assoc, SourceCohomology.relativeToSupportedSourceGlobalSections_inclusion]
  change AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections M X O ≫
      F.map (SectionQuasiIso.supportedSheafComplexMap O (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularSheafPullbackMap M f)) ≫ F.map i = _
  rw [← Functor.map_comp, SectionQuasiIso.supportedSheafComplexMap_inclusion, Functor.map_comp]
  change AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections M X O ≫
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion M X O ⊤ ≫
      F.map (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularSheafPullbackMap M f) = _
  rw [← Category.assoc, AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections_inclusion,
    Category.assoc, singularSheafPullback_global_unit]
  simpa only [Category.assoc] using (congrArg (fun g => g ≫ AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections M Y)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality M f
      (A := (((Opens.map f).obj O) : Set Y)) (B := (O : Set X)) (fun _ hy => hy))).symm

theorem supportedSourcePullback_cohomology [MetrizableSpace Y] (n : ℕ) :
    HomologicalComplex.homologyMap
        (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) X O) n ≫
      HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (⊤ : Opens X)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (supportedSourcePullback (ModuleCat.of ℚ ℚ) f O)) n ≫
        (SourceCohomology.supportedSourceGlobalCohomologyIso f O n).hom =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
      (A := (((Opens.map f).obj O) : Set Y)) (B := (O : Set X)) (fun _ hy => hy) n := by
  have := SourceCohomology.relativeToSupportedSourceGlobalSections_quasiIso f O
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    relativeToSupportedSourceGlobalSections_pullback, HomologicalComplex.homologyMap_comp,
    Category.assoc]
  change _ ≫ HomologicalComplex.homologyMap
      (SourceCohomology.relativeToSupportedSourceGlobalSections (ModuleCat.of ℚ ℚ) f O) n ≫
    (isoOfQuasiIsoAt (SourceCohomology.relativeToSupportedSourceGlobalSections (ModuleCat.of ℚ ℚ) f O) n).inv = _
  rw [isoOfQuasiIsoAt_hom_inv_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SourcePullback
