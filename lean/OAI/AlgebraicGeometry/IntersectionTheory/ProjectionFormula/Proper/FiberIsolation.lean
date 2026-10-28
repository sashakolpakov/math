import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.FiberIsolation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.SupportMinimal

/-! # Fiber Isolation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.FiberIsolation

noncomputable section

/-! Properness of an endpoint intersection supplies the isolated
native local-support hypothesis at every prescribed cycle support. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace IsLocalRing
open scoped _root_.Polynomial

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m d : ℕ)
  [hX : SmoothOfRelativeDimension m X.structureMap] {Y : Scheme}
  (u : X.carrier ⟶ Y) [IsClosedImmersion u] (t : Y ⟶ Spec (.of ℂ[X])) (a : ℂ)
  (hfiber : Set.range u = t ⁻¹' {Affine.ParameterFiber.point ℂ a})
  (A B : IrreducibleCloseds Y)

def intersection : Closeds X.carrier :=
  ⟨u ⁻¹' (A : Set Y) ∩ u ⁻¹' (B : Set Y),
    (A.isClosed.preimage u.continuous).inter (B.isClosed.preimage u.continuous)⟩

include hX hfiber

theorem isolated
    (hproper : ∀ D : IrreducibleCloseds X.carrier,
      (D : Set X.carrier) ⊆ intersection X u A B → d ≤ X.supportCodimension D)
    (C : X.DimensionCycleSupport d)
    (hxA : u (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) ∈ (A : Set Y)) (hxB : u (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) ∈ (B : Set Y)) :
    (Module.support (Y.presheaf.stalk (u (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)))
        (CycleClass.Thom.IntersectionGeometry.localSupportModule Y A (u (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) hxA) ∩
      Module.support (Y.presheaf.stalk (u (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)))
        (CycleClass.Thom.IntersectionGeometry.localSupportModule Y B (u (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) hxB)) ∩
      Module.support (Y.presheaf.stalk (u (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)))
        ((Y.presheaf.stalk (u (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))) ⧸
          Ideal.span {Affine.ParameterFiber.germ ℂ t (u (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) a}) ⊆
      {closedPoint (Y.presheaf.stalk (u (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)))} := by
  apply Closed.FiberIsolation.isolated u t a hfiber A B (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA hxB
  intro w hwA hwB hs
  exact SupportMinimal.minimal X m d (intersection X u A B) hproper C w ⟨hwA, hwB⟩ hs

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.FiberIsolation
