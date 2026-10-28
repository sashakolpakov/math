import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula

/-! # Reference Local Equation -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceLocalEquation.CM.ReferencePointFormula

/-! Original point equations yield the named source equation on
the canonically corresponding local points, with no point-matching premise. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.NeighborFormula.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ComparisonSpecialization.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  (M : Source.ComparisonModel.CM.SourceMap A) (T : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℚ_[q]))

theorem pointEquation_on_original_points
    (b : M.genericSource ⟶ A.variety.scheme)
    (F : Additive ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ (Geometric.ComparisonSpecialization.CM.varietyGroup A).X) →
      Additive ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ (Geometric.ComparisonSpecialization.CM.varietyGroup A).X))
    (x y : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource))
    (h : F (Additive.ofMul (x ≫ b) - Additive.ofMul (y ≫ b)) =
      (Nx.map (fun z => Additive.ofMul (z ≫ b))).sum -
        (Ny.map (fun z => Additive.ofMul (z ≫ b))).sum) :
    Source.ModelNeighborFormula.CM.PointEquation A M T b F (Local.NeighborFormula.CM.liftedNeighbor T M.sourceIso x)
      (Local.NeighborFormula.CM.liftedNeighbor T M.sourceIso y) Nx Ny := by
  simp only [Source.ModelNeighborFormula.CM.PointEquation, Local.NeighborFormula.CM.liftedNeighbor, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Equiv.apply_symm_apply]
  exact h

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceLocalEquation.CM.ReferencePointFormula

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceLocalEquation.CM.Reference

/-! The original point equation yields the local equation on its
canonical inverse images, using the proved source-map compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ModelNeighborFormula.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.NeighborFormula.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ComparisonSpecialization.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingPointAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  (M : Source.ComparisonModel.CM.SourceMap A) (T : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℚ_[q]))

def OriginalEquation (b : M.genericSource ⟶ A.variety.scheme)
    (F : Additive ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ (Geometric.ComparisonSpecialization.CM.varietyGroup A).X) →
      Additive ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ (Geometric.ComparisonSpecialization.CM.varietyGroup A).X))
    (x y : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource)) : Prop :=
  F (Additive.ofMul (x ≫ b) - Additive.ofMul (y ≫ b)) =
    (Nx.map (fun z => Additive.ofMul (z ≫ b))).sum -
      (Ny.map (fun z => Additive.ofMul (z ≫ b))).sum

def LocalOriginalEquation (f : A.ExtendingEndomorphism)
    (x y : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource)) : Prop :=
  Source.ModelNeighborFormula.CM.LocalEquation A M T f (Local.NeighborFormula.CM.liftedNeighbor T M.sourceIso x) (Local.NeighborFormula.CM.liftedNeighbor T M.sourceIso y) Nx Ny

theorem local_from_original (f : A.ExtendingEndomorphism)
    (b : M.genericSource ⟶ A.variety.scheme) (hb : M.genericMap = b)
    (F : Additive ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ (Geometric.ComparisonSpecialization.CM.varietyGroup A).X) →
      Additive ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ (Geometric.ComparisonSpecialization.CM.varietyGroup A).X))
    (hF : ∀ z, PointSpecializationFormula.CM.Points.evaluateAt (Geometric.ComparisonSpecialization.CM.varietyGroup A) ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T) (ExtendingPointAction.CM.genericEnd A f) z = F z)
    (x y : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ M.genericSource))
    (h : OriginalEquation A M T b F x y Nx Ny) : LocalOriginalEquation A M T f x y Nx Ny :=
  Source.ModelNeighborFormula.CM.localEquation_of_genericEquation A M T f _ _ Nx Ny
    (Source.ModelNeighborFormula.CM.genericEquation_of_named_point_formula A M T f b hb F hF _ _ Nx Ny
      (ReferencePointFormula.pointEquation_on_original_points A M T b F x y Nx Ny h))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceLocalEquation.CM.Reference

end

end OAI
