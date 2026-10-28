import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.ModuleStalk
import OAI.AlgebraicGeometry.Comparison.Betti.Module.StalkExact
import Mathlib.Algebra.Category.ModuleCat.Descent

/-! # Module Exact -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytification.ModuleExact

noncomputable section

/-! The original module analytification functor on a smooth integral
complex scheme is exact, by its actual stalk formula and flatness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Comparison.Betti.Module.StalkExact.Local

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

instance holomorphicModuleAnalytification_isLeftAdjoint :
    (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).IsLeftAdjoint :=
  (Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).isLeftAdjoint

instance holomorphicModuleAnalytification_additive :
    (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X)
  exact (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).additive_of_preservesBinaryBiproducts

theorem analytificationModuleStalk_preservesFiniteLimits (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    PreservesFiniteLimits (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X ⋙
      StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X) p) := by
  have hExt : PreservesFiniteLimits (ModuleCat.extendScalars (RingedStalk.analytificationRingedStalkMap X p)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (RingedStalk.analytificationRingedStalkMap_flat X p)
  have : PreservesFiniteLimits
      (StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of X.left) X.left.ringCatSheaf (Base.analytificationMap X p) ⋙
        ModuleCat.extendScalars (RingedStalk.analytificationRingedStalkMap X p)) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _
      (StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of X.left) X.left.ringCatSheaf (Base.analytificationMap X p))
      (ModuleCat.extendScalars (RingedStalk.analytificationRingedStalkMap X p)) inferInstance hExt
  exact preservesFiniteLimits_of_natIso (ModuleStalk.analytificationModuleStalkIso X p).symm

instance holomorphicModuleAnalytification_preservesMonomorphisms :
    (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).PreservesMonomorphisms where
  preserves {M N} f hf := by
    apply Module.StalkExact.Local.sheafModule_mono_of_stalk_mono
      (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (R := Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X)
    intro p
    have := analytificationModuleStalk_preservesFiniteLimits X p
    exact (inferInstance : Mono ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X ⋙
      StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X) p).map f))

instance holomorphicModuleAnalytification_preservesHomology :
    (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).PreservesHomology := by
  apply ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).exact_tfae.out 1 3).mp
  intro S hS
  have hRight : (S.map (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X)).Exact ∧
      Epi ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).map S.g) :=
    (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).preservesFiniteColimits_iff_forall_exact_map_and_epi.mp
      inferInstance S hS
  let : Mono S.f := hS.mono_f
  exact { exact := hRight.1
          mono_f := (inferInstance : Mono ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).map S.f))
          epi_g := hRight.2 }

instance holomorphicModuleAnalytification_preservesFiniteLimits :
    PreservesFiniteLimits (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X) :=
  (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).preservesFiniteLimits_of_preservesHomology

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytification.ModuleExact
