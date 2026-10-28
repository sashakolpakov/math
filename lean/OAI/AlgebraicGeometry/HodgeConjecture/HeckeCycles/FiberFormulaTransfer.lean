import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula

/-! # Fiber Formula Transfer -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberFormulaTransfer.CM

noncomputable section

/-! An equation on points over a commuting residue base is the same
equation for the actual base-changed endomorphism on the special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points

variable {S S' : Scheme} (b : S' ⟶ S) (T : Over S') (U : Over S)
  (e : (Over.map b).obj T ≅ U)

def fiberPoint (X : Over S) (x : U ⟶ X) : T ⟶ (Over.pullback b).obj X :=
  (BaseChangeEvaluation.CM.pointsEquiv b T X).symm (e.hom ≫ x)

theorem fiberPoint_evaluation (X : Over S) (x : U ⟶ X) :
    BaseChangeEvaluation.CM.pointsEquiv b T X (fiberPoint b T U e X x) = e.hom ≫ x :=
  (BaseChangeEvaluation.CM.pointsEquiv b T X).apply_symm_apply _

variable (G : CommGrp (Over S)) {X : Over S} (a : X ⟶ G.X)

theorem fiber_neighbor_formula (f : AbelianScheme.TateComparison.End.IntegralEnd G.X)
    (x y : U ⟶ X) (Nx Ny : Multiset (U ⟶ X))
    (h : PointSpecializationFormula.CM.Points.evaluateAt G U f (Additive.ofMul (x ≫ a) - Additive.ofMul (y ≫ a)) =
      (Nx.map (fun z => Additive.ofMul (z ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul (z ≫ a))).sum) :
    PointSpecializationFormula.CM.Points.evaluateAt (GroupBaseChange.CM.changedGroup G b) T (AbelianScheme.TateComparison.BaseChange.endBaseChange G.X b f)
      (BaseChangeEvaluation.CM.groupPoint b T G a (fiberPoint b T U e X x) -
        BaseChangeEvaluation.CM.groupPoint b T G a (fiberPoint b T U e X y)) =
      (Nx.map (fun z => BaseChangeEvaluation.CM.groupPoint b T G a (fiberPoint b T U e X z))).sum -
        (Ny.map (fun z => BaseChangeEvaluation.CM.groupPoint b T G a (fiberPoint b T U e X z))).sum := by
  let fp := fiberPoint b T U e X
  have he := PointSpecializationFormula.CM.Test.neighbor_formula G e.hom a f x y Nx Ny h
  have hf := BaseChangeEvaluation.CM.neighbor_formula b T G a f
    (fp x) (fp y) (Nx.map fp) (Ny.map fp) (by
      simpa only [Multiset.map_map, Function.comp_def, fp, fiberPoint_evaluation] using he)
  simpa only [Multiset.map_map, Function.comp_def, fp] using hf

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberFormulaTransfer.CM
