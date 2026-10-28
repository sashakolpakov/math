import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusPointAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberGeneration

/-! # End Points -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.EndPoints.CM

noncomputable section

/-! Evaluation of base-changed endomorphisms agrees with evaluation on
the original geometric point functor. The actual Frobenius therefore
has FrobeniusKernel's field-precomposition action after geometric base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberGeneration.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points

variable {S : Scheme} (G : CommGrp (Over S))
  {k : Type} [Field k] (b : Spec (.of k) ⟶ S)

theorem fiberPointsEquiv_evaluate (f : AbelianScheme.TateComparison.End.IntegralEnd G.X)
    (p : PointExt.CM.pointBase k ⟶ (AbelianScheme.TateComparison.BaseChange.baseChangedGroup G.X b).X) :
    FiberGeneration.CM.fiberPointsEquiv G.X b
      (PointSpecializationFormula.CM.Points.evaluateAt (AbelianScheme.TateComparison.BaseChange.baseChangedGroup G.X b) (PointExt.CM.pointBase k) (AbelianScheme.TateComparison.BaseChange.endBaseChange G.X b f)
        (Additive.ofMul p)).toMul =
      (PointSpecializationFormula.CM.Points.evaluateAt G (Over.mk b) f (Additive.ofMul (FiberGeneration.CM.fiberPointsEquiv G.X b p))).toMul := by
  exact (congrArg (FiberGeneration.CM.fiberPointsEquiv G.X b)
    (AbelianScheme.TateComparison.End.endSchemeMap_points (AbelianScheme.TateComparison.BaseChange.baseChangedGroup G.X b).X (AbelianScheme.TateComparison.BaseChange.endBaseChange G.X b f) (PointExt.CM.pointBase k) p)).trans
    ((congrArg (fun a => FiberGeneration.CM.fiberPointsEquiv G.X b (p ≫ a)) (AbelianScheme.TateComparison.BaseChange.endBaseChange_schemeMap G.X b f)).trans
      ((FiberGeneration.CM.fiberPointsEquiv_map (AbelianScheme.TateComparison.End.endSchemeMap G.X f) b p).trans
        (AbelianScheme.TateComparison.End.endSchemeMap_points G.X f (Over.mk b) (FiberGeneration.CM.fiberPointsEquiv G.X b p)).symm))

variable (q : ℕ) [Fact q.Prime]
  (A : CommGrp (Over (Spec (.of (ZMod q)))))

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FieldFrobenius.CM

theorem geometricFrobenius_point
    (p : PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q).hom).X) :
    FiberGeneration.CM.fiberPointsEquiv A.X (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q).hom
      (PointSpecializationFormula.CM.Points.evaluateAt (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q).hom) (PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))
        (AbelianScheme.TateComparison.BaseChange.endBaseChange A.X (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q).hom (Finite.FieldFrobenius.CM.integralFrobenius A)) (Additive.ofMul p)).toMul =
      (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫ FiberGeneration.CM.fiberPointsEquiv A.X (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q).hom p :=
  (fiberPointsEquiv_evaluate A (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q).hom (Finite.FieldFrobenius.CM.integralFrobenius A) p).trans
    (congrArg Additive.toMul (FrobeniusPointAction.CM.frobenius_evaluation q A
      (FiberGeneration.CM.fiberPointsEquiv A.X (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q).hom p)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.EndPoints.CM
