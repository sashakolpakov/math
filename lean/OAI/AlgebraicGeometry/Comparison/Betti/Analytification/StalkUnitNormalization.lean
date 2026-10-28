import OAI.AlgebraicGeometry.Comparison.Betti.Module.StalkUnitNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.ModuleStalk

/-! # Stalk Unit Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytification.StalkUnitNormalization

noncomputable section

/-! The actual module analytification stalk isomorphism carries the
germ of the original adjunction unit to the tensor-product unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Comparison.Betti.Module.StalkUnitNormalization.Local

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem analytificationModuleStalkIso_germ_unit (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (M : SheafOfModules.{0} X.left.ringCatSheaf) (U : X.left.Opens)
    (hp : Base.analytificationMap X p ∈ U) (m : M.val.obj (op U)) :
    (ModuleStalk.analytificationModuleStalkIso X p).hom.app M
        (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
          ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf
          (Open.AffineIsoEvaluation.analyticOpen X U) p hp
          (((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).unit.app M).val.app (op U) m)) =
      (ModuleCat.extendRestrictScalarsAdj (RingedStalk.analytificationRingedStalkMap X p)).unit.app
        ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of X.left) X.left.ringCatSheaf
          (Base.analytificationMap X p)).obj M)
        (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := TopCat.of X.left)
          M.val.presheaf U (Base.analytificationMap X p) hp m) := by
  let hCommR : IsMulCommutative (TopCat.Presheaf.stalk (C := RingCat)
      (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).obj p) :=
    inferInstanceAs (IsMulCommutative (ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X p))
  let hCommS : IsMulCommutative (TopCat.Presheaf.stalk (C := RingCat) (X := TopCat.of X.left)
      X.left.ringCatSheaf.obj (Base.analytificationMap X p)) :=
    inferInstanceAs (IsMulCommutative (RingedStalk.algebraicRingCatStalk X p))
  exact @Module.StalkUnitNormalization.Local.moduleStalkIsoOfAdjunction_germ_unit (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (TopCat.of X.left)
    (Base.analytificationMap X) (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X) X.left.ringCatSheaf
    (Holomorphic.StructureMorphism.holomorphicAnalytificationSite_continuous X) (Holomorphic.StructureMorphism.algebraicToHolomorphicStructureSheaf X) p
    hCommR hCommS (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X)
    (Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X) M U hp m

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytification.StalkUnitNormalization
