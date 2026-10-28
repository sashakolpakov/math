import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedNeighborSpecialization

/-! # Evaluated Formula -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.EvaluatedFormula.CM

noncomputable section

/-! The actual local source equation specializes over an evaluated
valuation ring. Its endomorphism is the specified integral extension,
and the reduced neighbors are defined by proper specialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ComparisonSpecialization.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingPointAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.NeighborFormula.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  (M : ComparisonModel.CM.SourceMap A) [IsProper M.integralSource.hom]
  {R L : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  (bR : Spec (.of R) ⟶ NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℤ_[q]) (c : Spec (.of L) ⟶ NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℚ_[q])
  (w : c ≫ NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]) = ValuativePoints.CM.genericBase (R := R) (L := L) ≫ bR)
  {k : Type} [Field k] (res : R →+* k)

local notation "eta" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q])
local notation "T" => Over.mk c
local notation "X" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM.localSource A M

local instance : GrpObj (Geometric.ComparisonSpecialization.CM.integralGroup A).X := (Geometric.ComparisonSpecialization.CM.integralGroup A).grp
local instance : IsCommMonObj (Geometric.ComparisonSpecialization.CM.integralGroup A).X := (Geometric.ComparisonSpecialization.CM.integralGroup A).comm
local instance : GrpObj (Geometric.ComparisonSpecialization.CM.localGroup A).X := (Geometric.ComparisonSpecialization.CM.localGroup A).grp
local instance : IsCommMonObj (Geometric.ComparisonSpecialization.CM.localGroup A).X := (Geometric.ComparisonSpecialization.CM.localGroup A).comm

def reducedSourcePoint (x : T ⟶ X) : ValuativePoints.CM.specialTest bR res ⟶ M.integralSource :=
  EvaluatedNeighborSpecialization.CM.reducedPoint eta bR c w res x

def reducedRawNeighbor (z : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource) :
    ValuativePoints.CM.specialTest bR res ⟶ M.integralSource :=
  reducedSourcePoint A M bR c w res (Local.NeighborFormula.CM.liftedNeighbor T M.sourceIso z)

def ReducedEquation (f : A.ExtendingEndomorphism) (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource)) : Prop :=
  PointSpecializationFormula.CM.Points.evaluateAt (Geometric.ComparisonSpecialization.CM.integralGroup A) (ValuativePoints.CM.specialTest bR res) (ExtendingPointAction.CM.integralEnd A f)
    (Additive.ofMul (reducedSourcePoint A M bR c w res x ≫ M.integralMap) -
      Additive.ofMul (reducedSourcePoint A M bR c w res y ≫ M.integralMap)) =
    (Nx.map (fun z => Additive.ofMul (reducedRawNeighbor A M bR c w res z ≫ M.integralMap))).sum -
      (Ny.map (fun z => Additive.ofMul (reducedRawNeighbor A M bR c w res z ≫ M.integralMap))).sum

theorem reducedEquation_of_localEquation (f : A.ExtendingEndomorphism) (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource))
    (h : ModelNeighborFormula.CM.LocalEquation A M T f x y Nx Ny) : ReducedEquation A M bR c w res f x y Nx Ny := by
  let lift := Local.NeighborFormula.CM.liftedNeighbor T M.sourceIso
  have hlocal : PointSpecializationFormula.CM.Points.evaluateAt (GroupBaseChange.CM.changedGroup (Geometric.ComparisonSpecialization.CM.integralGroup A) eta) T
      (AbelianScheme.TateComparison.BaseChange.endBaseChange (Geometric.ComparisonSpecialization.CM.integralGroup A).X eta (ExtendingPointAction.CM.integralEnd A f))
      (BaseChangeEvaluation.CM.groupPoint eta T (Geometric.ComparisonSpecialization.CM.integralGroup A) M.integralMap x -
        BaseChangeEvaluation.CM.groupPoint eta T (Geometric.ComparisonSpecialization.CM.integralGroup A) M.integralMap y) =
      ((Nx.map lift).map (BaseChangeEvaluation.CM.groupPoint eta T (Geometric.ComparisonSpecialization.CM.integralGroup A) M.integralMap)).sum -
        ((Ny.map lift).map (BaseChangeEvaluation.CM.groupPoint eta T (Geometric.ComparisonSpecialization.CM.integralGroup A) M.integralMap)).sum := by
    simp only [ModelNeighborFormula.CM.LocalEquation, ModelNeighborFormula.CM.localAlbaneseMap, ExtendingPointAction.CM.localEnd,
      NeronSpecialization.CM.genericRestriction, BaseChangeEvaluation.CM.groupPoint,
      Multiset.map_map, Function.comp_def, lift] at h ⊢
    exact h
  have hr := EvaluatedNeighborSpecialization.CM.reduced_neighbor_formula eta bR c w res
    (Geometric.ComparisonSpecialization.CM.integralGroup A) M.integralMap (ExtendingPointAction.CM.integralEnd A f) x y (Nx.map lift) (Ny.map lift) hlocal
  simp only [ReducedEquation, Multiset.map_map, Function.comp_def,
    reducedSourcePoint, reducedRawNeighbor, lift] at hr ⊢
  exact hr

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.EvaluatedFormula.CM
