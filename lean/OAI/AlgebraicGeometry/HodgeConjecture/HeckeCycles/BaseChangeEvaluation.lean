import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupFiberPoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula

/-! # Base Change Evaluation -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation.CM

/-! Evaluation compatibility for base-changed groups on an arbitrary
test scheme. This includes algebraic-closure points over the q-adic field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupFiberPoints.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points

variable {S S' : Scheme} (b : S' ⟶ S) (T : Over S')

def pointsEquiv (X : Over S) :
    (T ⟶ (Over.pullback b).obj X) ≃ ((Over.map b).obj T ⟶ X) :=
  ((Over.mapPullbackAdj b).homEquiv T X).symm

theorem pointsEquiv_map {X Y : Over S} (a : X ⟶ Y)
    (x : T ⟶ (Over.pullback b).obj X) :
    pointsEquiv b T Y (x ≫ (Over.pullback b).map a) = pointsEquiv b T X x ≫ a :=
  (Over.mapPullbackAdj b).homEquiv_naturality_right_symm x a

variable (G : CommGrp (Over S))

local instance : GrpObj (GroupBaseChange.CM.changedGroup G b).X := (GroupBaseChange.CM.changedGroup G b).grp
local instance : IsCommMonObj (GroupBaseChange.CM.changedGroup G b).X := (GroupBaseChange.CM.changedGroup G b).comm

def pointsAddEquiv : Additive (T ⟶ (GroupBaseChange.CM.changedGroup G b).X) ≃+
    Additive ((Over.map b).obj T ⟶ G.X) :=
  (GroupFiberPoints.CM.baseChangePointsMulEquiv G b T).toAdditive

def groupPoint {X : Over S} (a : X ⟶ G.X) (x : T ⟶ (Over.pullback b).obj X) :
    Additive (T ⟶ (GroupBaseChange.CM.changedGroup G b).X) := Additive.ofMul (x ≫ (Over.pullback b).map a)

theorem pointsAddEquiv_groupPoint {X : Over S} (a : X ⟶ G.X)
    (x : T ⟶ (Over.pullback b).obj X) :
    pointsAddEquiv b T G (groupPoint b T G a x) = Additive.ofMul (pointsEquiv b T X x ≫ a) :=
  congrArg Additive.ofMul (pointsEquiv_map b T a x)

theorem pointsAddEquiv_evaluate (f : AbelianScheme.TateComparison.End.IntegralEnd G.X)
    (x : Additive (T ⟶ (GroupBaseChange.CM.changedGroup G b).X)) :
    pointsAddEquiv b T G (PointSpecializationFormula.CM.Points.evaluateAt (GroupBaseChange.CM.changedGroup G b) T (AbelianScheme.TateComparison.BaseChange.endBaseChange G.X b f) x) =
      PointSpecializationFormula.CM.Points.evaluateAt G ((Over.map b).obj T) f (pointsAddEquiv b T G x) := by
  have he : PointSpecializationFormula.CM.Points.evaluateAt (GroupBaseChange.CM.changedGroup G b) T (AbelianScheme.TateComparison.BaseChange.endBaseChange G.X b f) x =
      groupPoint b T G (AbelianScheme.TateComparison.End.endSchemeMap G.X f) x.toMul := by
    apply Additive.toMul.injective
    exact (@AbelianScheme.TateComparison.End.endSchemeMap_points _ (GroupBaseChange.CM.changedGroup G b).X
      (GroupBaseChange.CM.changedGroup G b).grp (GroupBaseChange.CM.changedGroup G b).comm (AbelianScheme.TateComparison.BaseChange.endBaseChange G.X b f) T x.toMul).trans
      (congrArg (x.toMul ≫ ·) (AbelianScheme.TateComparison.BaseChange.endBaseChange_schemeMap G.X b f))
  refine (congrArg (pointsAddEquiv b T G) he).trans ?_
  refine (pointsAddEquiv_groupPoint b T G (AbelianScheme.TateComparison.End.endSchemeMap G.X f) x.toMul).trans ?_
  apply Additive.toMul.injective
  exact (AbelianScheme.TateComparison.End.endSchemeMap_points G.X f ((Over.map b).obj T) (pointsEquiv b T G.X x.toMul)).symm

theorem neighbor_formula {X : Over S} (a : X ⟶ G.X) (f : AbelianScheme.TateComparison.End.IntegralEnd G.X)
    (x y : T ⟶ (Over.pullback b).obj X)
    (Nx Ny : Multiset (T ⟶ (Over.pullback b).obj X))
    (h : PointSpecializationFormula.CM.Points.evaluateAt G ((Over.map b).obj T) f
      (Additive.ofMul (pointsEquiv b T X x ≫ a) - Additive.ofMul (pointsEquiv b T X y ≫ a)) =
      (Nx.map (fun z => Additive.ofMul (pointsEquiv b T X z ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul (pointsEquiv b T X z ≫ a))).sum) :
    PointSpecializationFormula.CM.Points.evaluateAt (GroupBaseChange.CM.changedGroup G b) T (AbelianScheme.TateComparison.BaseChange.endBaseChange G.X b f)
      (groupPoint b T G a x - groupPoint b T G a y) =
      (Nx.map (groupPoint b T G a)).sum - (Ny.map (groupPoint b T G a)).sum := by
  apply (pointsAddEquiv b T G).injective
  rw [pointsAddEquiv_evaluate b T G f (groupPoint b T G a x - groupPoint b T G a y)]
  simpa only [map_sub, map_multiset_sum, Multiset.map_map, Function.comp_def,
    pointsAddEquiv_groupPoint] using h

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation.CM.FormulaDescent

/-! Read a point formula on a base-changed group back on its original
model via the actual pullback adjunction. Every multiset term is retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation.CM

variable {S S' : Scheme} (b : S' ⟶ S) (T : Over S') (G : CommGrp (Over S))
  {X : Over S} (a : X ⟶ G.X)

theorem neighbor_sum (N : Multiset (T ⟶ (Over.pullback b).obj X)) :
    pointsAddEquiv b T G ((N.map (groupPoint b T G a)).sum) =
      (N.map (fun z => Additive.ofMul (pointsEquiv b T X z ≫ a))).sum := by
  rw [map_multiset_sum, Multiset.map_map]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro z _
  exact pointsAddEquiv_groupPoint b T G a z

theorem original_neighbor_formula (f : AbelianScheme.TateComparison.End.IntegralEnd G.X)
    (x y : T ⟶ (Over.pullback b).obj X)
    (Nx Ny : Multiset (T ⟶ (Over.pullback b).obj X))
    (h : PointSpecializationFormula.CM.Points.evaluateAt (GroupBaseChange.CM.changedGroup G b) T (AbelianScheme.TateComparison.BaseChange.endBaseChange G.X b f)
      (groupPoint b T G a x - groupPoint b T G a y) =
      (Nx.map (groupPoint b T G a)).sum - (Ny.map (groupPoint b T G a)).sum) :
    PointSpecializationFormula.CM.Points.evaluateAt G ((Over.map b).obj T) f
      (Additive.ofMul (pointsEquiv b T X x ≫ a) - Additive.ofMul (pointsEquiv b T X y ≫ a)) =
      (Nx.map (fun z => Additive.ofMul (pointsEquiv b T X z ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul (pointsEquiv b T X z ≫ a))).sum := by
  have he := congrArg (pointsAddEquiv b T G) h
  rw [pointsAddEquiv_evaluate b T G f (groupPoint b T G a x - groupPoint b T G a y)] at he
  simpa only [map_sub, pointsAddEquiv_groupPoint, neighbor_sum] using he

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation.CM.FormulaDescent

end

end OAI
