import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.NeighborFormula
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel

/-! # Model Neighbor Formula -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM

noncomputable section

/-! Use the compatibility proved by the source-map constructor directly
when transporting the original generic neighbor formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ComparisonSpecialization.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingPointAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.NeighborFormula.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  (M : ComparisonModel.CM.SourceMap A) (T : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℚ_[q]))

abbrev localSource := (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))).obj M.integralSource
abbrev localAlbaneseMap := (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))).map M.integralMap

local notation "X" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM.localSource A M
local notation "a" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM.localAlbaneseMap A M

theorem source_model_neighbor_formula
    (f : A.ExtendingEndomorphism) (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource))
    (h : PointSpecializationFormula.CM.Points.evaluateAt (Geometric.ComparisonSpecialization.CM.varietyGroup A) ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T) (ExtendingPointAction.CM.genericEnd A f)
      (Additive.ofMul (BaseChangeEvaluation.CM.pointsEquiv (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) T M.genericSource (x ≫ M.sourceIso.hom) ≫ M.genericMap) -
        Additive.ofMul (BaseChangeEvaluation.CM.pointsEquiv (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) T M.genericSource (y ≫ M.sourceIso.hom) ≫ M.genericMap)) =
      (Nx.map (fun z => Additive.ofMul (z ≫ M.genericMap))).sum -
        (Ny.map (fun z => Additive.ofMul (z ≫ M.genericMap))).sum) :
    PointSpecializationFormula.CM.Points.evaluateAt (Geometric.ComparisonSpecialization.CM.localGroup A) T (ExtendingPointAction.CM.localEnd A f) (Additive.ofMul (x ≫ a) - Additive.ofMul (y ≫ a)) =
      (Nx.map (fun z => Additive.ofMul (Local.NeighborFormula.CM.liftedNeighbor T M.sourceIso z ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul (Local.NeighborFormula.CM.liftedNeighbor T M.sourceIso z ≫ a))).sum :=
  Local.NeighborFormula.CM.local_neighbor_formula A T M.sourceIso a M.genericMap M.compatible f x y Nx Ny h

def GenericEquation (f : A.ExtendingEndomorphism) (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource)) : Prop :=
  PointSpecializationFormula.CM.Points.evaluateAt (Geometric.ComparisonSpecialization.CM.varietyGroup A) ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T) (ExtendingPointAction.CM.genericEnd A f)
    (Additive.ofMul (BaseChangeEvaluation.CM.pointsEquiv (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) T M.genericSource (x ≫ M.sourceIso.hom) ≫ M.genericMap) -
      Additive.ofMul (BaseChangeEvaluation.CM.pointsEquiv (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) T M.genericSource (y ≫ M.sourceIso.hom) ≫ M.genericMap)) =
    (Nx.map (fun z => Additive.ofMul (z ≫ M.genericMap))).sum -
      (Ny.map (fun z => Additive.ofMul (z ≫ M.genericMap))).sum

def LocalEquation (f : A.ExtendingEndomorphism) (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource)) : Prop :=
  PointSpecializationFormula.CM.Points.evaluateAt (Geometric.ComparisonSpecialization.CM.localGroup A) T (ExtendingPointAction.CM.localEnd A f) (Additive.ofMul (x ≫ a) - Additive.ofMul (y ≫ a)) =
    (Nx.map (fun z => Additive.ofMul (Local.NeighborFormula.CM.liftedNeighbor T M.sourceIso z ≫ a))).sum -
      (Ny.map (fun z => Additive.ofMul (Local.NeighborFormula.CM.liftedNeighbor T M.sourceIso z ≫ a))).sum

theorem genericEquation_of_point_formula (f : A.ExtendingEndomorphism)
    (b : M.genericSource ⟶ A.variety.scheme) (hb : M.genericMap = b)
    (F : Additive ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ (Geometric.ComparisonSpecialization.CM.varietyGroup A).X) →
      Additive ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ (Geometric.ComparisonSpecialization.CM.varietyGroup A).X))
    (hF : ∀ z, PointSpecializationFormula.CM.Points.evaluateAt (Geometric.ComparisonSpecialization.CM.varietyGroup A) ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T) (ExtendingPointAction.CM.genericEnd A f) z = F z)
    (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource))
    (h : F
      (Additive.ofMul (BaseChangeEvaluation.CM.pointsEquiv (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) T M.genericSource (x ≫ M.sourceIso.hom) ≫ b) -
        Additive.ofMul (BaseChangeEvaluation.CM.pointsEquiv (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) T M.genericSource (y ≫ M.sourceIso.hom) ≫ b)) =
      (Nx.map (fun z => Additive.ofMul (z ≫ b))).sum -
        (Ny.map (fun z => Additive.ofMul (z ≫ b))).sum) :
    GenericEquation A M T f x y Nx Ny := by
  subst b
  exact (hF _).trans h

def PointEquation
    (b : M.genericSource ⟶ A.variety.scheme)
    (F : Additive ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ (Geometric.ComparisonSpecialization.CM.varietyGroup A).X) →
      Additive ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ (Geometric.ComparisonSpecialization.CM.varietyGroup A).X))
    (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource)) : Prop :=
  F
    (Additive.ofMul (BaseChangeEvaluation.CM.pointsEquiv (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) T M.genericSource (x ≫ M.sourceIso.hom) ≫ b) -
      Additive.ofMul (BaseChangeEvaluation.CM.pointsEquiv (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) T M.genericSource (y ≫ M.sourceIso.hom) ≫ b)) =
    (Nx.map (fun z => Additive.ofMul (z ≫ b))).sum -
      (Ny.map (fun z => Additive.ofMul (z ≫ b))).sum

theorem genericEquation_of_named_point_formula (f : A.ExtendingEndomorphism)
    (b : M.genericSource ⟶ A.variety.scheme) (hb : M.genericMap = b)
    (F : Additive ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ (Geometric.ComparisonSpecialization.CM.varietyGroup A).X) →
      Additive ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ (Geometric.ComparisonSpecialization.CM.varietyGroup A).X))
    (hF : ∀ z, PointSpecializationFormula.CM.Points.evaluateAt (Geometric.ComparisonSpecialization.CM.varietyGroup A) ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T) (ExtendingPointAction.CM.genericEnd A f) z = F z)
    (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource))
    (h : PointEquation A M T b F x y Nx Ny) : GenericEquation A M T f x y Nx Ny :=
  genericEquation_of_point_formula A M T f b hb F hF x y Nx Ny h

theorem localEquation_of_genericEquation (f : A.ExtendingEndomorphism) (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource))
    (h : GenericEquation A M T f x y Nx Ny) : LocalEquation A M T f x y Nx Ny :=
  source_model_neighbor_formula A M T f x y Nx Ny h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM
