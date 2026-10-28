import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ComparisonSpecialization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointFormulaTransport

/-! # Extending Point Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingPointAction.CM

noncomputable section

/-! The integral extension's generic point action is the original
number-field action, under the exact GeometricComparison generic comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ComparisonSpecialization.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeronSpecialization.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndTransportCM.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointFormulaTransport.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)

local instance : GrpObj (Geometric.ComparisonSpecialization.CM.localGroup A).X := (Geometric.ComparisonSpecialization.CM.localGroup A).grp
local instance : IsCommMonObj (Geometric.ComparisonSpecialization.CM.localGroup A).X := (Geometric.ComparisonSpecialization.CM.localGroup A).comm
local instance : GrpObj (Geometric.ComparisonSpecialization.CM.completedVarietyGroup A).X := (Geometric.ComparisonSpecialization.CM.completedVarietyGroup A).grp
local instance : IsCommMonObj (Geometric.ComparisonSpecialization.CM.completedVarietyGroup A).X := (Geometric.ComparisonSpecialization.CM.completedVarietyGroup A).comm
local instance : IsMonHom (Geometric.ComparisonSpecialization.CM.genericIdentification A).hom := Geometric.ComparisonSpecialization.CM.genericIdentification_group A
local instance : IsMonHom (Geometric.ComparisonSpecialization.CM.genericIdentification A).symm.hom := Geometric.ComparisonSpecialization.CM.genericIdentification_inv_group A

def integralEnd (f : A.ExtendingEndomorphism) : AbelianScheme.TateComparison.End.IntegralEnd (Geometric.ComparisonSpecialization.CM.integralGroup A).X :=
  (EndomorphismComparison.CM.integralEquiv A.integral.scheme).symm f.integral

def genericEnd (f : A.ExtendingEndomorphism) : AbelianScheme.TateComparison.End.IntegralEnd (Geometric.ComparisonSpecialization.CM.varietyGroup A).X :=
  (EndomorphismComparison.CM.integralEquiv A.variety.scheme).symm f.generic

def localEnd (f : A.ExtendingEndomorphism) : AbelianScheme.TateComparison.End.IntegralEnd (Geometric.ComparisonSpecialization.CM.localGroup A).X :=
  NeronSpecialization.CM.genericRestriction (K := ℚ_[q]) (Geometric.ComparisonSpecialization.CM.integralGroup A) (integralEnd A f)

theorem transport_localEnd (f : A.ExtendingEndomorphism) :
    EndTransportCM.CM.transport (Geometric.ComparisonSpecialization.CM.genericIdentification A) (localEnd A f) =
      AbelianScheme.TateComparison.BaseChange.endBaseChange (Geometric.ComparisonSpecialization.CM.varietyGroup A).X (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) (genericEnd A f) := by
  let fc : AbelianScheme.TateComparison.End.IntegralEnd (Geometric.ComparisonSpecialization.CM.completedVarietyGroup A).X :=
    AbelianScheme.TateComparison.BaseChange.endBaseChange (Geometric.ComparisonSpecialization.CM.varietyGroup A).X (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) (genericEnd A f)
  have h : EndTransportCM.CM.transport (Geometric.ComparisonSpecialization.CM.genericIdentification A) ((EndTransportCM.CM.transport (Geometric.ComparisonSpecialization.CM.genericIdentification A)).symm fc) =
      EndTransportCM.CM.transport (Geometric.ComparisonSpecialization.CM.genericIdentification A) (localEnd A f) :=
    congrArg (EndTransportCM.CM.transport (Geometric.ComparisonSpecialization.CM.genericIdentification A)) (Geometric.ComparisonSpecialization.CM.completedEnd_extending A f)
  exact h.symm.trans ((EndTransportCM.CM.transport (Geometric.ComparisonSpecialization.CM.genericIdentification A)).apply_symm_apply fc)

variable (T : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℚ_[q]))

def localToGenericPoints : Additive (T ⟶ (Geometric.ComparisonSpecialization.CM.localGroup A).X) ≃+
    Additive ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T ⟶ (Geometric.ComparisonSpecialization.CM.varietyGroup A).X) :=
  (PointFormulaTransport.CM.postcomposeAddEquiv (Geometric.ComparisonSpecialization.CM.localGroup A) (Geometric.ComparisonSpecialization.CM.completedVarietyGroup A) (Geometric.ComparisonSpecialization.CM.genericIdentification A) T).trans
    (BaseChangeEvaluation.CM.pointsAddEquiv (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) T (Geometric.ComparisonSpecialization.CM.varietyGroup A))

theorem localToGenericPoints_evaluate (f : A.ExtendingEndomorphism)
    (x : Additive (T ⟶ (Geometric.ComparisonSpecialization.CM.localGroup A).X)) :
    localToGenericPoints A T (PointSpecializationFormula.CM.Points.evaluateAt (Geometric.ComparisonSpecialization.CM.localGroup A) T (localEnd A f) x) =
      PointSpecializationFormula.CM.Points.evaluateAt (Geometric.ComparisonSpecialization.CM.varietyGroup A) ((Over.map (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj T) (genericEnd A f)
        (localToGenericPoints A T x) := by
  change BaseChangeEvaluation.CM.pointsAddEquiv (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) T (Geometric.ComparisonSpecialization.CM.varietyGroup A)
    (PointFormulaTransport.CM.postcomposeAddEquiv (Geometric.ComparisonSpecialization.CM.localGroup A) (Geometric.ComparisonSpecialization.CM.completedVarietyGroup A) (Geometric.ComparisonSpecialization.CM.genericIdentification A) T
      (PointSpecializationFormula.CM.Points.evaluateAt (Geometric.ComparisonSpecialization.CM.localGroup A) T (localEnd A f) x)) = _
  rw [PointFormulaTransport.CM.postcompose_evaluate, transport_localEnd]
  exact BaseChangeEvaluation.CM.pointsAddEquiv_evaluate (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) T (Geometric.ComparisonSpecialization.CM.varietyGroup A) (genericEnd A f) _

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingPointAction.CM
