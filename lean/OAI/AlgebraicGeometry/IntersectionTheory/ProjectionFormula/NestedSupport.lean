import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImmersionSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Nested Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport

noncomputable section

/-! Canonical closed immersions between nested reduced cycle supports,
with their actual generic points and the induced inner support scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Scheme) (A W : IrreducibleCloseds X) (hAW : A ≤ W)

def inclusion : CycleClass.Geometric.GenericPoint.reducedSupportScheme A ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme W :=
  Scheme.IdealSheafData.inclusion (Scheme.IdealSheafData.vanishingIdeal_antimono
    (show (⟨(A : Set X), A.isClosed⟩ : Closeds X) ≤ ⟨(W : Set X), W.isClosed⟩ from hAW))

instance : IsClosedImmersion (NestedSupport.inclusion X A W hAW) := by
  unfold NestedSupport.inclusion
  infer_instance

theorem inclusion_fac : NestedSupport.inclusion X A W hAW ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W = CycleClass.Geometric.GenericPoint.reducedSupportι A :=
  Scheme.IdealSheafData.inclusion_subschemeι _

theorem inclusion_preimage (x : X) (hxA : x ∈ (A : Set X)) (hxW : x ∈ (W : Set X)) :
    NestedSupport.inclusion X A W hAW (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA) = CycleClass.Thom.IntersectionGeometry.supportPreimage W x hxW := by
  apply (CycleClass.Geometric.GenericPoint.reducedSupportι W).isEmbedding.injective
  have h := congrArg (fun f : CycleClass.Geometric.GenericPoint.reducedSupportScheme A ⟶ X => f (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA))
    (inclusion_fac X A W hAW)
  exact h.trans ((CycleClass.Thom.IntersectionGeometry.supportPreimage_spec A x hxA).trans (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hxW).symm)

theorem inclusion_genericPoint :
    NestedSupport.inclusion X A W hAW (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme A)) =
      CycleClass.Thom.IntersectionGeometry.supportPreimage W (CycleClass.Thom.IntersectionGeometry.supportPoint A)
        (hAW (A.isIrreducible.isGenericPoint_genericPoint A.isClosed).mem) := by
  apply (CycleClass.Geometric.GenericPoint.reducedSupportι W).isEmbedding.injective
  have h := congrArg (fun f : CycleClass.Geometric.GenericPoint.reducedSupportScheme A ⟶ X => f (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme A)))
    (inclusion_fac X A W hAW)
  exact h.trans ((CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq A).trans (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W _ _).symm)

def innerSupport : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) :=
  Closed.ImmersionSupport.support (NestedSupport.inclusion X A W hAW)

theorem innerSupport_point :
    CycleClass.Thom.IntersectionGeometry.supportPoint (innerSupport X A W hAW) = CycleClass.Thom.IntersectionGeometry.supportPreimage W (CycleClass.Thom.IntersectionGeometry.supportPoint A)
      (hAW (A.isIrreducible.isGenericPoint_genericPoint A.isClosed).mem) :=
  (Closed.ImmersionSupport.support_point (NestedSupport.inclusion X A W hAW)).trans
    (inclusion_genericPoint X A W hAW)

def innerSupportIso : CycleClass.Geometric.GenericPoint.reducedSupportScheme A ≅ CycleClass.Geometric.GenericPoint.reducedSupportScheme (innerSupport X A W hAW) :=
  Closed.ImmersionSupport.supportIso (NestedSupport.inclusion X A W hAW)

theorem innerSupportIso_fac :
    (innerSupportIso X A W hAW).hom ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (innerSupport X A W hAW) =
      NestedSupport.inclusion X A W hAW := Closed.ImmersionSupport.supportIso_fac _

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport
