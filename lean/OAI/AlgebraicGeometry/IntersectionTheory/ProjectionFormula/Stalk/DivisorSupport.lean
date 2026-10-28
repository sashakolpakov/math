import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.Localization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.Stalk

/-! # Divisor Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

noncomputable section

/-! Height-one primes at a codimension-two intersection give actual
dimension-graded divisor supports in the ambient smooth projective scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

def primeClosure (X : Scheme) (x : X) (p : Spec (X.presheaf.stalk x)) :
    IrreducibleCloseds X := irreducibleSetEquivPoints.symm (X.fromSpecStalk x p)

theorem primeClosure_point (X : Scheme) (x : X) (p : Spec (X.presheaf.stalk x)) :
    CycleClass.Thom.IntersectionGeometry.supportPoint (primeClosure X x p) = X.fromSpecStalk x p :=
  irreducibleSetEquivPoints.apply_symm_apply _

theorem point_mem_primeClosure (X : Scheme) (x : X) (p : Spec (X.presheaf.stalk x)) :
    x ∈ (primeClosure X x p : Set X) := by
  have h : X.fromSpecStalk x p ⤳ x := by
    simpa only [Scheme.fromSpecStalk_closedPoint] using
      (IsLocalRing.specializes_closedPoint p).map (X.fromSpecStalk x).continuous
  exact h.mem_closed (primeClosure X x p).isClosed
    (subset_closure (Set.mem_singleton _))

theorem primeClosure_codimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport 1) (C : X.DimensionCycleSupport 2) (hCA : C.val ≤ A.val)
    (p : Spec (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))) (hp : p.asIdeal.height = 1) :
    X.supportCodimension (primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) = 1 := by
  let W := primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p
  have hW : coheight (CycleClass.Thom.IntersectionGeometry.supportPoint W) = 1 := by
    rw [primeClosure_point, ← Localization.height_eq_coheight_image]
    exact hp
  have hCW : C.val ≤ W :=
    (Supports.supportPoint_mem_iff_subset
      (⟨(W : Set X.carrier), W.isClosed⟩ : Closeds X.carrier) C.val).mp
      (point_mem_primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p)
  have hn : C.val ≠ W := by
    intro he
    have hC := Divisor.Stalk.coheight_two X m A C hCA
    rw [he, hW] at hC
    exact (by decide : (1 : ℕ∞) ≠ 2) hC
  have hlt := Supports.codimension_strictAnti X m (lt_of_le_of_ne hCW hn)
  rw [C.property] at hlt
  have hlo := CurveSupports.coheight_le_codimension X m W
  rw [hW] at hlo
  have hpos : 1 ≤ X.supportCodimension W := by exact_mod_cast hlo
  change X.supportCodimension W = 1
  omega

def divisorSupport (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport 1) (C : X.DimensionCycleSupport 2) (hCA : C.val ≤ A.val)
    (p : Spec (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))) (hp : p.asIdeal.height = 1) :
    X.DimensionCycleSupport 1 :=
  ⟨primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p, primeClosure_codimension X m A C hCA p hp⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport
