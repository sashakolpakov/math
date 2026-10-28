import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecializedPointFormula

/-! # Evaluated Neighbor Specialization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedNeighborSpecialization.CM

noncomputable section

/-! Specialize a generic-fiber point formula through a commuting valued
base diagram. The evaluated and reduced points are constructed from the
pullback adjunction and properness, retaining the entire neighbor multiset. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM

variable {R L : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  {S S' : Scheme} (d : S' ⟶ S) (bR : Spec (.of R) ⟶ S) (c : Spec (.of L) ⟶ S')
  (w : c ≫ d = ValuativePoints.CM.genericBase (R := R) (L := L) ≫ bR)

def evaluatedTestMap : ValuativePoints.CM.genericTest (L := L) bR ⟶ (Over.map d).obj (Over.mk c) :=
  Over.homMk (𝟙 _) ((Category.id_comp (c ≫ d)).trans w)

def evaluatedPoint (X : Over S) (x : Over.mk c ⟶ (Over.pullback d).obj X) :
    ValuativePoints.CM.genericTest (L := L) bR ⟶ X :=
  evaluatedTestMap d bR c w ≫ BaseChangeEvaluation.CM.pointsEquiv d (Over.mk c) X x

variable {k : Type} [Field k] (res : R →+* k)
  (G : CommGrp (Over S)) [IsProper G.X.hom]
  {X : Over S} [IsProper X.hom] (a : X ⟶ G.X)

def reducedPoint (x : Over.mk c ⟶ (Over.pullback d).obj X) : ValuativePoints.CM.specialTest bR res ⟶ X :=
  ValuativePoints.CM.specializePoint bR res X (evaluatedPoint d bR c w X x)

theorem reduced_neighbor_formula (f : AbelianScheme.TateComparison.End.IntegralEnd G.X)
    (x y : Over.mk c ⟶ (Over.pullback d).obj X)
    (Nx Ny : Multiset (Over.mk c ⟶ (Over.pullback d).obj X))
    (h : PointSpecializationFormula.CM.Points.evaluateAt (GroupBaseChange.CM.changedGroup G d) (Over.mk c) (AbelianScheme.TateComparison.BaseChange.endBaseChange G.X d f)
      (BaseChangeEvaluation.CM.groupPoint d (Over.mk c) G a x - BaseChangeEvaluation.CM.groupPoint d (Over.mk c) G a y) =
      (Nx.map (BaseChangeEvaluation.CM.groupPoint d (Over.mk c) G a)).sum -
        (Ny.map (BaseChangeEvaluation.CM.groupPoint d (Over.mk c) G a)).sum) :
    PointSpecializationFormula.CM.Points.evaluateAt G (ValuativePoints.CM.specialTest bR res) f
      (Additive.ofMul (reducedPoint d bR c w res x ≫ a) -
        Additive.ofMul (reducedPoint d bR c w res y ≫ a)) =
      (Nx.map (fun z => Additive.ofMul (reducedPoint d bR c w res z ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul (reducedPoint d bR c w res z ≫ a))).sum := by
  let px := BaseChangeEvaluation.CM.pointsEquiv d (Over.mk c) X
  let py := evaluatedPoint d bR c w X
  have h0 := BaseChangeEvaluation.CM.FormulaDescent.original_neighbor_formula d (Over.mk c) G a f x y Nx Ny h
  have h1 := PointSpecializationFormula.CM.Test.neighbor_formula G (evaluatedTestMap d bR c w) a f
    (px x) (px y) (Nx.map px) (Ny.map px)
    (by simpa only [Multiset.map_map, Function.comp_def, px] using h0)
  have h2 : PointSpecializationFormula.CM.Points.evaluateAt G (ValuativePoints.CM.genericTest bR) f
      (Additive.ofMul (py x ≫ a) - Additive.ofMul (py y ≫ a)) =
      ((Nx.map py).map (fun z => Additive.ofMul (z ≫ a))).sum -
        ((Ny.map py).map (fun z => Additive.ofMul (z ≫ a))).sum := by
    simpa only [Multiset.map_map, Function.comp_def, px, py, evaluatedPoint] using h1
  have h3 := SpecializedPointFormula.CM.specialized_neighbor_formula bR G res a f
    (py x) (py y) (Nx.map py) (Ny.map py) h2
  simpa only [Multiset.map_map, Function.comp_def, reducedPoint, py] using h3

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedNeighborSpecialization.CM
