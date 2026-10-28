import OAI.AlgebraicGeometry.Comparison.Betti.Module.PullbackStalk
import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.RingedStalk

/-! # Module Stalk -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytification.ModuleStalk

noncomputable section

/-! The original algebraic-to-holomorphic module analytification has
native stalks given by extension along its actual structure map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Comparison.Betti.Module.PullbackStalk.Local

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def analytificationModuleStalkIso (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X ⋙
        StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
          (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X) p ≅
      StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of X.left) X.left.ringCatSheaf (Base.analytificationMap X p) ⋙
        ModuleCat.extendScalars (RingedStalk.analytificationRingedStalkMap X p) := by
  let hCommR : IsMulCommutative (TopCat.Presheaf.stalk (C := RingCat)
      (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).obj p) :=
    inferInstanceAs (IsMulCommutative (ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X p))
  let hCommS : IsMulCommutative (TopCat.Presheaf.stalk (C := RingCat) (X := TopCat.of X.left)
      X.left.ringCatSheaf.obj (Base.analytificationMap X p)) :=
    inferInstanceAs (IsMulCommutative (RingedStalk.algebraicRingCatStalk X p))
  exact @Module.PullbackStalk.Local.moduleStalkIsoOfAdjunction (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (TopCat.of X.left)
    (Base.analytificationMap X) (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X) X.left.ringCatSheaf
    (Holomorphic.StructureMorphism.holomorphicAnalytificationSite_continuous X) (Holomorphic.StructureMorphism.algebraicToHolomorphicStructureSheaf X) p
    hCommR hCommS (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X)
    (Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytification.ModuleStalk
