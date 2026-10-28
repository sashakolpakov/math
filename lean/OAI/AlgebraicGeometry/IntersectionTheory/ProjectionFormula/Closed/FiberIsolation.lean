import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.ParameterFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricSupportLocalization

/-! # Fiber Isolation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.FiberIsolation

noncomputable section

/-! Minimality of an endpoint intersection point gives the exact
isolated-support hypothesis for the ambient parameter specialization formula. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace IsLocalRing
open scoped _root_.Polynomial

variable {X Y : Scheme} (u : X ⟶ Y) [IsClosedImmersion u]
  (t : Y ⟶ Spec (.of ℂ[X])) (a : ℂ)
  (hfiber : Set.range u = t ⁻¹' {Affine.ParameterFiber.point ℂ a})
  (A B : IrreducibleCloseds Y) (x : X)
  (hxA : u x ∈ (A : Set Y)) (hxB : u x ∈ (B : Set Y))
  (hminimal : ∀ w : X, u w ∈ (A : Set Y) → u w ∈ (B : Set Y) → w ⤳ x → w = x)

include hfiber hminimal

theorem isolated :
    (Module.support (Y.presheaf.stalk (u x)) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y A (u x) hxA) ∩
      Module.support (Y.presheaf.stalk (u x)) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y B (u x) hxB)) ∩
      Module.support (Y.presheaf.stalk (u x))
        ((Y.presheaf.stalk (u x)) ⧸ Ideal.span {Affine.ParameterFiber.germ ℂ t (u x) a}) ⊆
      {closedPoint (Y.presheaf.stalk (u x))} := by
  rintro p ⟨⟨hpA, hpB⟩, hpr⟩
  have hr : Affine.ParameterFiber.germ ℂ t (u x) a ∈ p.asIdeal := by
    rw [Module.support_of_algebra, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] at hpr
    exact hpr (Ideal.subset_span (Set.mem_singleton _))
  have hf : t (Y.fromSpecStalk (u x) p) = Affine.ParameterFiber.point ℂ a :=
    (Local.ParameterFiber.mem_iff t (u x) p a).mp hr
  obtain ⟨w, hw⟩ := (hfiber.symm ▸ hf : Y.fromSpecStalk (u x) p ∈ Set.range u)
  have hwA : u w ∈ (A : Set Y) := hw.symm ▸
    (GeometricSupportLocalization.mem_iff Y A (u x) hxA p).mp hpA
  have hwB : u w ∈ (B : Set Y) := hw.symm ▸
    (GeometricSupportLocalization.mem_iff Y B (u x) hxB p).mp hpB
  have hs : w ⤳ x := by
    apply u.isEmbedding.isInducing.specializes_iff.mp
    rw [hw]
    simpa only [Scheme.fromSpecStalk_closedPoint] using
      (specializes_closedPoint p).map (Y.fromSpecStalk (u x)).continuous
  have he := hminimal w hwA hwB hs
  apply Set.mem_singleton_iff.mpr
  apply (Y.fromSpecStalk (u x)).isEmbedding.injective
  rw [Scheme.fromSpecStalk_closedPoint, ← hw, he]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.FiberIsolation
