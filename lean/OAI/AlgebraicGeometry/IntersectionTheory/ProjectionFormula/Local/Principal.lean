import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Order

/-! # Principal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

noncomputable section

/-! ThomClass's exact native intersection multiplicity equals the order of a
local equation when one reduced support has a regular principal ideal and
that equation does not vanish identically on the other support. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Pointwise

def supportStalkMap (X : Scheme) (W : IrreducibleCloseds X) (x : X)
    (hx : x ∈ (W : Set X)) :
    X.presheaf.stalk x ⟶ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx) :=
  eqToHom (congrArg (fun t => X.presheaf.stalk t) (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hx).symm) ≫
    (CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx)

theorem supportStalkMap_surjective (X : Scheme) (W : IrreducibleCloseds X) (x : X)
    (hx : x ∈ (W : Set X)) : Function.Surjective (supportStalkMap X W x hx) :=
  ((CycleClass.Geometric.GenericPoint.reducedSupportι W).stalkMap_surjective _).comp
    (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg
      (fun t => X.presheaf.stalk t) (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hx).symm))).surjective

theorem intersectionMultiplicity_eq_order (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B C : IrreducibleCloseds X.carrier)
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (A : Set X.carrier)) (hxB : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (B : Set X.carrier))
    (r : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C)) (hr : r ≠ 0)
    (hB : RingHom.ker (supportStalkMap X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxB).hom = Ideal.span {r})
    (hAr : supportStalkMap X.carrier A (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxA r ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A B C =
      (Ring.ord ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxA))
        (supportStalkMap X.carrier A (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxA r)).toNat := by
  let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C)
  let S := (CycleClass.Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxA)
  let T := (CycleClass.Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage B (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxB)
  let σ := supportStalkMap X.carrier A (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxA
  let τ := supportStalkMap X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxB
  let : Algebra R S := σ.hom.toAlgebra
  let : Algebra R T := τ.hom.toAlgebra
  let : IsDomain R := X.stalk_isDomain (CycleClass.Thom.IntersectionGeometry.supportPoint C)
  have hσ : Function.Surjective (algebraMap R S) := supportStalkMap_surjective X.carrier A _ hxA
  have hτ : Function.Surjective (Algebra.ofId R T) := supportStalkMap_surjective X.carrier B _ hxB
  have hI : RingHom.ker (Algebra.ofId R T) = r • (⊤ : Submodule R R) := by
    change RingHom.ker τ.hom = _
    rw [hB, ← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  let e : CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxB ≃ₗ[R] QuotSMulTop r R :=
    (Ideal.quotientKerAlgEquivOfSurjective hτ).symm.toLinearEquiv.trans
      (Submodule.quotEquivOfEq _ _ hI)
  have hr' : IsSMulRegular R r := fun _ _ h => mul_left_cancel₀ hr h
  rw [CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_left ⟨hxA, hxB⟩]
  exact Principal.Order.euler_eq_order_of_equiv R S hσ r hr' hAr
    (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxB) e X.ambientDimension

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal
