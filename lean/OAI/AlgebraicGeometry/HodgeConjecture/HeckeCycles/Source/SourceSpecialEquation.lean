import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.EvaluatedFormula
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberFormulaTransfer
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialEndEvaluation

/-! # Source Special Equation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SourceSpecialEquation.CM

noncomputable section

/-! The reduced source equation holds on the actual prime-field
special fiber with the identical GeometricComparison specialized endomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ComparisonSpecialization.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.EvaluatedFormula.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingPointAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberFormulaTransfer.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialEndEvaluation.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  (M : ComparisonModel.CM.SourceMap A) [IsProper M.integralSource.hom]
  {R L : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  (bR : Spec (.of R) ⟶ NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℤ_[q]) (c : Spec (.of L) ⟶ NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℚ_[q])
  (w : c ≫ NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]) = ValuativePoints.CM.genericBase (R := R) (L := L) ≫ bR)
  {k : Type} [Field k] (res : R →+* k)
  (U : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase (ZMod q)))
  (e : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))).obj U ≅ ValuativePoints.CM.specialTest bR res)

local notation "red" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q)
local notation "T" => Over.mk c
local notation "X" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM.localSource A M

abbrev specialSource := (Over.pullback red).obj M.integralSource
abbrev specialGroup := GroupBaseChange.CM.changedGroup (Geometric.ComparisonSpecialization.CM.integralGroup A) red

local instance : GrpObj (specialGroup A).X := (specialGroup A).grp
local instance : IsCommMonObj (specialGroup A).X := (specialGroup A).comm
local instance : GrpObj (Geometric.ComparisonSpecialization.CM.integralGroup A).X := (Geometric.ComparisonSpecialization.CM.integralGroup A).grp
local instance : IsCommMonObj (Geometric.ComparisonSpecialization.CM.integralGroup A).X := (Geometric.ComparisonSpecialization.CM.integralGroup A).comm

def specialPoint (x : T ⟶ X) : U ⟶ specialSource A M :=
  FiberFormulaTransfer.CM.fiberPoint red U (ValuativePoints.CM.specialTest bR res) e M.integralSource
    (EvaluatedFormula.CM.reducedSourcePoint A M bR c w res x)

def specialNeighbor (z : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource) :
    U ⟶ specialSource A M :=
  FiberFormulaTransfer.CM.fiberPoint red U (ValuativePoints.CM.specialTest bR res) e M.integralSource
    (EvaluatedFormula.CM.reducedRawNeighbor A M bR c w res z)

def SpecialEquation (f : A.ExtendingEndomorphism) (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource)) : Prop :=
  PointSpecializationFormula.CM.Points.evaluateAt (specialGroup A) U
    ((EndomorphismComparison.CM.integralEquiv A.specialFiber.scheme).symm (Geometric.ComparisonSpecialization.CM.specializeEnd A f.generic))
    (Additive.ofMul (specialPoint A M bR c w res U e x ≫ (Over.pullback red).map M.integralMap) -
      Additive.ofMul (specialPoint A M bR c w res U e y ≫ (Over.pullback red).map M.integralMap)) =
    (Nx.map (fun z => Additive.ofMul
      (specialNeighbor A M bR c w res U e z ≫ (Over.pullback red).map M.integralMap))).sum -
    (Ny.map (fun z => Additive.ofMul
      (specialNeighbor A M bR c w res U e z ≫ (Over.pullback red).map M.integralMap))).sum

theorem specialEquation_of_reducedEquation (f : A.ExtendingEndomorphism) (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource))
    (h : EvaluatedFormula.CM.ReducedEquation A M bR c w res f x y Nx Ny) :
    SpecialEquation A M bR c w res U e f x y Nx Ny := by
  let px := EvaluatedFormula.CM.reducedSourcePoint A M bR c w res
  let pn := EvaluatedFormula.CM.reducedRawNeighbor A M bR c w res
  have he := FiberFormulaTransfer.CM.fiber_neighbor_formula red U (ValuativePoints.CM.specialTest bR res) e
    (Geometric.ComparisonSpecialization.CM.integralGroup A) M.integralMap (ExtendingPointAction.CM.integralEnd A f)
    (px x) (px y) (Nx.map pn) (Ny.map pn) (by
      simp only [EvaluatedFormula.CM.ReducedEquation, Multiset.map_map, Function.comp_def, px, pn] at h ⊢
      exact h)
  change PointSpecializationFormula.CM.Points.evaluateAt (specialGroup A) U (SpecialEndEvaluation.CM.specialIntegralEnd A f) _ = _ at he
  rw [SpecialEndEvaluation.CM.specialIntegralEnd_eq] at he
  simp only [SpecialEquation, Multiset.map_map, Function.comp_def,
    BaseChangeEvaluation.CM.groupPoint, specialPoint, specialNeighbor, px, pn] at he ⊢
  exact he

theorem specialEquation_of_localEquation (f : A.ExtendingEndomorphism) (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource))
    (h : ModelNeighborFormula.CM.LocalEquation A M T f x y Nx Ny) :
    SpecialEquation A M bR c w res U e f x y Nx Ny :=
  specialEquation_of_reducedEquation A M bR c w res U e f x y Nx Ny
    (EvaluatedFormula.CM.reducedEquation_of_localEquation A M bR c w res f x y Nx Ny h)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SourceSpecialEquation.CM
