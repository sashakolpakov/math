import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.EndPoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndTransportCM
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FieldFrobenius

/-! # Transported Geometric Points -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TransportedGeometricPoints.CM

noncomputable section

/-! Geometric point evaluation is compatible with the actual group
isomorphisms used to transport the special-fiber endomorphism ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberGeneration.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points

theorem transport_evaluation_inv {S : Scheme} (A B : CommGrp (Over S))
    (e : A.X ≅ B.X) [IsMonHom e.hom] (T : Over S) (p : T ⟶ B.X) (f : AbelianScheme.TateComparison.End.IntegralEnd A.X) :
    (PointSpecializationFormula.CM.Points.evaluateAt B T (EndTransportCM.CM.transport e f) (Additive.ofMul p)).toMul ≫ e.inv =
      (PointSpecializationFormula.CM.Points.evaluateAt A T f (Additive.ofMul (p ≫ e.inv))).toMul := by
  have h₁ : (PointSpecializationFormula.CM.Points.evaluateAt B T (EndTransportCM.CM.transport e f) (Additive.ofMul p)).toMul ≫ e.inv =
      (p ≫ (e.inv ≫ AbelianScheme.TateComparison.End.endSchemeMap A.X f ≫ e.hom)) ≫ e.inv :=
    (congrArg (· ≫ e.inv) (AbelianScheme.TateComparison.End.endSchemeMap_points B.X (EndTransportCM.CM.transport e f) T p)).trans
      (congrArg (fun u => (p ≫ u) ≫ e.inv) (EndTransportCM.CM.transport_schemeMap e f))
  have h₂ : (p ≫ (e.inv ≫ AbelianScheme.TateComparison.End.endSchemeMap A.X f ≫ e.hom)) ≫ e.inv =
      (p ≫ e.inv) ≫ AbelianScheme.TateComparison.End.endSchemeMap A.X f := by
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h₃ : (p ≫ e.inv) ≫ AbelianScheme.TateComparison.End.endSchemeMap A.X f =
      (PointSpecializationFormula.CM.Points.evaluateAt A T f (Additive.ofMul (p ≫ e.inv))).toMul :=
    (AbelianScheme.TateComparison.End.endSchemeMap_points A.X f T (p ≫ e.inv)).symm
  exact h₁.trans (h₂.trans h₃)

variable (q : ℕ) [Fact q.Prime]
  (A : CommGrp (Over (Spec (.of (ZMod q)))))

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FieldFrobenius.CM

def geometricScalarBase : Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)) ⟶ Spec (.of (ZMod q)) :=
  (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q).hom

variable (B : CommGrp (Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)))))
  (e : (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (geometricScalarBase q)).X ≅ B.X)

local instance : GrpObj (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (geometricScalarBase q)).X :=
  (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (geometricScalarBase q)).grp
local instance : IsCommMonObj (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (geometricScalarBase q)).X :=
  (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (geometricScalarBase q)).comm
local instance : GrpObj B.X := B.grp
local instance : IsCommMonObj B.X := B.comm

def pointEquiv : (Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ B.X) ≃ (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ A.X) :=
  (Iso.homCongr (Iso.refl (Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) e.symm).trans
    (FiberGeneration.CM.fiberPointsEquiv A.X (geometricScalarBase q))

theorem pointEquiv_apply (p : Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ B.X) :
    pointEquiv q A B e p = FiberGeneration.CM.fiberPointsEquiv A.X (geometricScalarBase q) (p ≫ e.inv) := by
  change FiberGeneration.CM.fiberPointsEquiv A.X (geometricScalarBase q) ((𝟙 _ ≫ p) ≫ e.inv) = _
  exact congrArg (FiberGeneration.CM.fiberPointsEquiv A.X (geometricScalarBase q))
    (congrArg (· ≫ e.inv) (Category.id_comp p))

variable [he : IsMonHom e.hom]

theorem pointEquiv_frobenius (p : Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ B.X) :
    pointEquiv q A B e
      (PointSpecializationFormula.CM.Points.evaluateAt B (Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))
        (EndTransportCM.CM.transport e
          (AbelianScheme.TateComparison.BaseChange.endBaseChange A.X (geometricScalarBase q) (Finite.FieldFrobenius.CM.integralFrobenius A))) (Additive.ofMul p)).toMul =
      (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫ pointEquiv q A B e p := by
  have ht := transport_evaluation_inv (AbelianScheme.TateComparison.BaseChange.baseChangedGroup A.X (geometricScalarBase q)) B e
    (Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)) p (AbelianScheme.TateComparison.BaseChange.endBaseChange A.X (geometricScalarBase q) (Finite.FieldFrobenius.CM.integralFrobenius A))
  change FiberGeneration.CM.fiberPointsEquiv A.X (geometricScalarBase q)
    ((𝟙 _ ≫ (PointSpecializationFormula.CM.Points.evaluateAt B (Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))
      (EndTransportCM.CM.transport e
        (AbelianScheme.TateComparison.BaseChange.endBaseChange A.X (geometricScalarBase q) (Finite.FieldFrobenius.CM.integralFrobenius A))) (Additive.ofMul p)).toMul) ≫
      e.inv) = (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫
        FiberGeneration.CM.fiberPointsEquiv A.X (geometricScalarBase q) ((𝟙 _ ≫ p) ≫ e.inv)
  simp only [Category.id_comp]
  exact (congrArg (FiberGeneration.CM.fiberPointsEquiv A.X (geometricScalarBase q)) ht).trans
    (Geometric.EndPoints.CM.geometricFrobenius_point q A (p ≫ e.inv))

theorem pointEquiv_transportedFrobenius (p : Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ B.X) :
    pointEquiv q A B e
      (PointEvaluationCM.CM.pointAction B.X
        ((@Finite.FieldFrobenius.CM.transportedGeometricEndAction (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) _ _
          A (algebraMap (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)) B e he).val
          (Finite.FieldFrobenius.CM.integralFrobenius A)) (Additive.ofMul p)).toMul =
      (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫ pointEquiv q A B e p :=
  pointEquiv_frobenius q A B e p

local instance : GrpObj (GroupBaseChange.CM.changedGroup A (geometricScalarBase q)).X :=
  (GroupBaseChange.CM.changedGroup A (geometricScalarBase q)).grp
local instance : IsCommMonObj (GroupBaseChange.CM.changedGroup A (geometricScalarBase q)).X :=
  (GroupBaseChange.CM.changedGroup A (geometricScalarBase q)).comm

omit he in
theorem pointEquiv_groupFrobenius
    (g : (GroupBaseChange.CM.changedGroup A (geometricScalarBase q)).toGrp ≅ B.toGrp)
    (p : Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ B.X) :
    let e : (GroupBaseChange.CM.changedGroup A (geometricScalarBase q)).X ≅ B.X :=
      (Grp.forget _).mapIso g
    letI : IsMonHom e.hom := g.hom.hom.isMonHom_hom
    pointEquiv q A B e
      (PointEvaluationCM.CM.pointAction B.X
        ((@Finite.FieldFrobenius.CM.transportedGeometricEndAction (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) _ _
          A (algebraMap (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)) B e g.hom.hom.isMonHom_hom).val
          (Finite.FieldFrobenius.CM.integralFrobenius A)) (Additive.ofMul p)).toMul =
      (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫ pointEquiv q A B e p := by
  let e : (GroupBaseChange.CM.changedGroup A (geometricScalarBase q)).X ≅ B.X :=
    (Grp.forget _).mapIso g
  let : IsMonHom e.hom := g.hom.hom.isMonHom_hom
  exact @pointEquiv_transportedFrobenius q _ A B e (g.hom.hom.isMonHom_hom) p

omit he in
theorem pointEquiv_groupEmbeddingFrobenius
    (g : (GroupBaseChange.CM.changedGroup A (geometricScalarBase q)).toGrp ≅ B.toGrp)
    (p : Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ B.X) :
    pointEquiv q A B ((Grp.forget _).mapIso g)
      (PointEvaluationCM.CM.pointAction B.X
        ((Finite.FieldFrobenius.CM.GroupEndAction.embedding A (algebraMap (ZMod q) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)) B g).val
          (Finite.FieldFrobenius.CM.integralFrobenius A)) (Additive.ofMul p)).toMul =
      (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫ pointEquiv q A B ((Grp.forget _).mapIso g) p :=
  pointEquiv_groupFrobenius q A B g p

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TransportedGeometricPoints.CM
