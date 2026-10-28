import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupFiberPoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TransportedGeometricPoints

/-! # Point Transport Detection -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointTransportDetection.CM.TransportedAddEquiv

/-! The canonical geometric point comparison is an additive equivalence,
so it preserves ordinary differences and zero-detection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TransportedGeometricPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberGeneration.CM

variable (q : ℕ) [Fact q.Prime]
  (A : CommGrp (Over (Spec (.of (ZMod q)))))
  (B : CommGrp (Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)))))
  (e : (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (TransportedGeometricPoints.CM.geometricScalarBase q)).X ≅ B.X)

local instance : GrpObj (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (TransportedGeometricPoints.CM.geometricScalarBase q)).X :=
  (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (TransportedGeometricPoints.CM.geometricScalarBase q)).grp
local instance : IsCommMonObj (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (TransportedGeometricPoints.CM.geometricScalarBase q)).X :=
  (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (TransportedGeometricPoints.CM.geometricScalarBase q)).comm
local instance : GrpObj B.X := B.grp
local instance : IsCommMonObj B.X := B.comm

variable [IsMonHom e.hom]

def pointAddEquiv :
    Additive (Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ B.X) ≃+
      Additive (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ A.X) where
  toFun x := Additive.ofMul (TransportedGeometricPoints.CM.pointEquiv q A B e x.toMul)
  invFun x := Additive.ofMul ((TransportedGeometricPoints.CM.pointEquiv q A B e).symm x.toMul)
  left_inv x := congrArg Additive.ofMul ((TransportedGeometricPoints.CM.pointEquiv q A B e).symm_apply_apply x.toMul)
  right_inv x := congrArg Additive.ofMul ((TransportedGeometricPoints.CM.pointEquiv q A B e).apply_symm_apply x.toMul)
  map_add' x y := by
    apply Additive.toMul.injective
    change TransportedGeometricPoints.CM.pointEquiv q A B e (x.toMul * y.toMul) =
      TransportedGeometricPoints.CM.pointEquiv q A B e x.toMul * TransportedGeometricPoints.CM.pointEquiv q A B e y.toMul
    simp only [TransportedGeometricPoints.CM.pointEquiv_apply]
    rw [MonObj.mul_comp]
    exact (GroupFiberPoints.CM.fiberMulEquiv A (TransportedGeometricPoints.CM.geometricScalarBase q)).map_mul _ _

theorem pointAddEquiv_apply (x : Additive (Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ B.X)) :
    (pointAddEquiv q A B e x).toMul = TransportedGeometricPoints.CM.pointEquiv q A B e x.toMul := rfl

theorem pointEquiv_evaluate (f : AbelianScheme.TateComparison.End.IntegralEnd A.X)
    (p : Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ B.X) :
    TransportedGeometricPoints.CM.pointEquiv q A B e
      (PointSpecializationFormula.CM.Points.evaluateAt B (Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))
        (EndTransportCM.CM.transport e (AbelianScheme.TateComparison.BaseChange.endBaseChange A.X (TransportedGeometricPoints.CM.geometricScalarBase q) f))
          (Additive.ofMul p)).toMul =
      (PointSpecializationFormula.CM.Points.evaluateAt A (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q) f (Additive.ofMul (TransportedGeometricPoints.CM.pointEquiv q A B e p))).toMul := by
  have h := TransportedGeometricPoints.CM.transport_evaluation_inv (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (TransportedGeometricPoints.CM.geometricScalarBase q)) B e
    (Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)) p (AbelianScheme.TateComparison.BaseChange.endBaseChange A.X (TransportedGeometricPoints.CM.geometricScalarBase q) f)
  simp only [TransportedGeometricPoints.CM.pointEquiv_apply]
  exact (congrArg (FiberGeneration.CM.fiberPointsEquiv A.X (TransportedGeometricPoints.CM.geometricScalarBase q)) h).trans
    (Geometric.EndPoints.CM.fiberPointsEquiv_evaluate A (TransportedGeometricPoints.CM.geometricScalarBase q) f (p ≫ e.inv))

theorem pointAddEquiv_evaluate (f : AbelianScheme.TateComparison.End.IntegralEnd A.X)
    (x : Additive (Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ B.X)) :
    pointAddEquiv q A B e
      (PointSpecializationFormula.CM.Points.evaluateAt B (Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))
        (EndTransportCM.CM.transport e (AbelianScheme.TateComparison.BaseChange.endBaseChange A.X (TransportedGeometricPoints.CM.geometricScalarBase q) f)) x) =
      PointSpecializationFormula.CM.Points.evaluateAt A (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q) f (pointAddEquiv q A B e x) := by
  apply Additive.toMul.injective
  exact pointEquiv_evaluate q A B e f x.toMul

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointTransportDetection.CM.TransportedAddEquiv

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointTransportDetection.CM

/-! Faithful geometric detection transfers along the genuine additive
point equivalence and faithful field extension of endomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TransportedGeometricPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointTransportDetection.CM.TransportedAddEquiv OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FieldFrobenius.CM

variable (q : ℕ) [Fact q.Prime]
  (A : CommGrp (Over (Spec (.of (ZMod q)))))
  (B : CommGrp (Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)))))
  (e : (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (TransportedGeometricPoints.CM.geometricScalarBase q)).X ≅ B.X)

local instance : GrpObj (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (TransportedGeometricPoints.CM.geometricScalarBase q)).X :=
  (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (TransportedGeometricPoints.CM.geometricScalarBase q)).grp
local instance : IsCommMonObj (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (TransportedGeometricPoints.CM.geometricScalarBase q)).X :=
  (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (TransportedGeometricPoints.CM.geometricScalarBase q)).comm
local instance : GrpObj B.X := B.grp
local instance : IsCommMonObj B.X := B.comm

variable [he : IsMonHom e.hom]

theorem detection_transfer {O J : Type*} (component : O → J)
    (β : O → Additive (Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ B.X))
    (α : O → Additive (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ A.X))
    (hpoints : ∀ x, TransportedAddEquiv.pointAddEquiv q A B e (β x) = α x)
    (hdetect : ∀ f : AbelianScheme.TateComparison.End.IntegralEnd B.X,
      (∀ x y : O, component x = component y →
        PointSpecializationFormula.CM.Points.evaluateAt B (Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)) f (β x - β y) = 0) → f = 0)
    (f : AbelianScheme.TateComparison.End.IntegralEnd A.X)
    (h : ∀ x y : O, component x = component y →
      PointSpecializationFormula.CM.Points.evaluateAt A (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q) f (α x - α y) = 0) : f = 0 := by
  let ρ := @Finite.FieldFrobenius.CM.transportedGeometricEndAction (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) _ _
    A (algebraMap (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)) B e he
  apply ρ.property
  rw [map_zero]
  apply hdetect
  intro x y hxy
  apply (TransportedAddEquiv.pointAddEquiv q A B e).injective
  calc
    _ = PointSpecializationFormula.CM.Points.evaluateAt A (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q) f (TransportedAddEquiv.pointAddEquiv q A B e (β x - β y)) :=
      TransportedAddEquiv.pointAddEquiv_evaluate q A B e f (β x - β y)
    _ = PointSpecializationFormula.CM.Points.evaluateAt A (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q) f (α x - α y) := by rw [map_sub, hpoints, hpoints]
    _ = 0 := h x y hxy
    _ = _ := (map_zero (TransportedAddEquiv.pointAddEquiv q A B e)).symm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointTransportDetection.CM

end

end OAI
