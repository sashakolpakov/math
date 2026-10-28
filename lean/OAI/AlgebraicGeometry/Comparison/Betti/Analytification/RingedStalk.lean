import OAI.AlgebraicGeometry.Comparison.Betti.CommRingStalkForget
import OAI.AlgebraicGeometry.Comparison.Betti.Module.RingedStalkPushforward
import OAI.AlgebraicGeometry.Comparison.Betti.ConcreteHolomorphicStalkFlatness

/-! # Ringed Stalk -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytification.RingedStalk

noncomputable section

/-! The ring map in the native module pullback is the original
regular-to-holomorphic local ring map after forgetting commutativity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped IsMulCommutative

open OAI.AlgebraicGeometry.Comparison.Betti.CommRingStalkForget.AnalyticLocal

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

abbrev algebraicRingCatStalk (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : RingCat :=
  TopCat.Presheaf.stalk (C := RingCat) (X := TopCat.of X.left)
    X.left.ringCatSheaf.obj (Base.analytificationMap X p)

instance algebraicRingCatStalkCommRing (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    CommRing (algebraicRingCatStalk X p) :=
  { (inferInstance : Ring (algebraicRingCatStalk X p)) with
    mul_comm := fun a b =>
      (CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv X.left.presheaf (Base.analytificationMap X p)).injective
        (((CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv X.left.presheaf (Base.analytificationMap X p)).map_mul a b).trans
          ((mul_comm _ _).trans
            ((CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv X.left.presheaf (Base.analytificationMap X p)).map_mul b a).symm)) }

def analytificationRingedStalkMap (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    algebraicRingCatStalk X p →+* ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X p :=
  Module.RingedStalkPushforward.Local.ringedStalkMap (Base.analytificationMap X) (R := (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).obj)
    (S := X.left.ringCatSheaf.obj) (Holomorphic.StructureMorphism.algebraicToHolomorphicStructureSheaf X).hom p

theorem analytificationRingedStalkMap_eq (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    analytificationRingedStalkMap X p =
      (ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap X p).comp
        (CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv X.left.presheaf (Base.analytificationMap X p)).toRingHom := by
  apply RingHom.ext
  intro a
  change _ = analytificationRingedStalkMap X p
    ((CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv X.left.presheaf (Base.analytificationMap X p)).symm
      ((CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv X.left.presheaf (Base.analytificationMap X p)) a))
  exact congrArg (analytificationRingedStalkMap X p)
    ((CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv X.left.presheaf (Base.analytificationMap X p)).symm_apply_apply a).symm

theorem analytificationRingedStalkMap_flat (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    (analytificationRingedStalkMap X p).Flat := by
  rw [analytificationRingedStalkMap_eq]
  exact (RingHom.Flat.of_bijective
      (f := (CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv X.left.presheaf (Base.analytificationMap X p)).toRingHom)
      (CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv X.left.presheaf
      (Base.analytificationMap X p)).bijective).comp (ConcreteHolomorphicStalkFlatness.algebraicHolomorphicStalkMap_flat X p)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytification.RingedStalk
