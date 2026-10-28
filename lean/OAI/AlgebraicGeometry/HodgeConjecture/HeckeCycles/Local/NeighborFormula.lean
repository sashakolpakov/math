import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingPointAction

/-! # Neighbor Formula -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.NeighborFormula.CM

noncomputable section

/-! The original number-field neighbor formula transfers to the generic
fiber of the integral comparison model. All point identifications are
the pullback adjunction and the actual source and Albanese isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ComparisonSpecialization.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointFormulaTransport.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingPointAction.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  (T : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℚ_[q])) {X : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℚ_[q])} {Y : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase K)}
  (u : X ≅ (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj Y)

local instance : GrpObj (Geometric.ComparisonSpecialization.CM.localGroup A).X := (Geometric.ComparisonSpecialization.CM.localGroup A).grp
local instance : IsCommMonObj (Geometric.ComparisonSpecialization.CM.localGroup A).X := (Geometric.ComparisonSpecialization.CM.localGroup A).comm
local instance : GrpObj (Geometric.ComparisonSpecialization.CM.completedVarietyGroup A).X := (Geometric.ComparisonSpecialization.CM.completedVarietyGroup A).grp
local instance : IsCommMonObj (Geometric.ComparisonSpecialization.CM.completedVarietyGroup A).X := (Geometric.ComparisonSpecialization.CM.completedVarietyGroup A).comm
local instance : IsMonHom (Geometric.ComparisonSpecialization.CM.genericIdentification A).hom := Geometric.ComparisonSpecialization.CM.genericIdentification_group A

def liftedNeighbor (z : (Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ Y) : T ⟶ X :=
  (BaseChangeEvaluation.CM.pointsEquiv (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) T Y).symm z ≫ u.inv

theorem local_neighbor_formula
    (a : X ⟶ (Geometric.ComparisonSpecialization.CM.localGroup A).X) (b : Y ⟶ (Geometric.ComparisonSpecialization.CM.varietyGroup A).X)
    (hnatural : a ≫ (Geometric.ComparisonSpecialization.CM.genericIdentification A).hom = u.hom ≫ (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).map b)
    (f : A.ExtendingEndomorphism) (x y : T ⟶ X)
    (Nx Ny : Multiset ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ Y))
    (h : PointSpecializationFormula.CM.Points.evaluateAt (Geometric.ComparisonSpecialization.CM.varietyGroup A) ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T) (ExtendingPointAction.CM.genericEnd A f)
      (Additive.ofMul (BaseChangeEvaluation.CM.pointsEquiv (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) T Y (x ≫ u.hom) ≫ b) -
        Additive.ofMul (BaseChangeEvaluation.CM.pointsEquiv (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) T Y (y ≫ u.hom) ≫ b)) =
      (Nx.map (fun z => Additive.ofMul (z ≫ b))).sum -
        (Ny.map (fun z => Additive.ofMul (z ≫ b))).sum) :
    PointSpecializationFormula.CM.Points.evaluateAt (Geometric.ComparisonSpecialization.CM.localGroup A) T (ExtendingPointAction.CM.localEnd A f) (Additive.ofMul (x ≫ a) - Additive.ofMul (y ≫ a)) =
      (Nx.map (fun z => Additive.ofMul (liftedNeighbor T u z ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul (liftedNeighbor T u z ≫ a))).sum := by
  let px := BaseChangeEvaluation.CM.pointsEquiv (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) T Y
  let Nxc := Nx.map px.symm
  let Nyc := Ny.map px.symm
  have hc := BaseChangeEvaluation.CM.neighbor_formula (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) T (Geometric.ComparisonSpecialization.CM.varietyGroup A) b (ExtendingPointAction.CM.genericEnd A f)
    (x ≫ u.hom) (y ≫ u.hom) Nxc Nyc (by
      simpa only [Nxc, Nyc, Multiset.map_map, Function.comp_def, px,
        Equiv.apply_symm_apply] using h)
  let fc : AbelianScheme.TateComparison.End.IntegralEnd (Geometric.ComparisonSpecialization.CM.completedVarietyGroup A).X :=
    AbelianScheme.TateComparison.BaseChange.endBaseChange (Geometric.ComparisonSpecialization.CM.varietyGroup A).X (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) (ExtendingPointAction.CM.genericEnd A f)
  have he : EndTransportCM.CM.transport (Geometric.ComparisonSpecialization.CM.genericIdentification A) (ExtendingPointAction.CM.localEnd A f) = fc :=
    ExtendingPointAction.CM.transport_localEnd A f
  have hp := PointFormulaTransport.CM.transported_neighbor_formula (Geometric.ComparisonSpecialization.CM.localGroup A) (Geometric.ComparisonSpecialization.CM.completedVarietyGroup A)
    (Geometric.ComparisonSpecialization.CM.genericIdentification A) T u a ((Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).map b) hnatural
    (ExtendingPointAction.CM.localEnd A f) x y Nxc Nyc (by
      exact (congrArg (fun ff : AbelianScheme.TateComparison.End.IntegralEnd (Geometric.ComparisonSpecialization.CM.completedVarietyGroup A).X =>
        PointSpecializationFormula.CM.Points.evaluateAt (Geometric.ComparisonSpecialization.CM.completedVarietyGroup A) T ff
          (Additive.ofMul ((x ≫ u.hom) ≫ (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).map b) -
            Additive.ofMul ((y ≫ u.hom) ≫ (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).map b))) he).trans hc)
  simpa only [Nxc, Nyc, Multiset.map_map, Function.comp_def, liftedNeighbor, px] using hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.NeighborFormula.CM
