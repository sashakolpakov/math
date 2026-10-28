import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.PrincipalIntersectionOrder
import OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Symmetry

/-! # Principal Intersection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.PrincipalIntersection

noncomputable section

/-! ThomClass's exact native intersection multiplicity equals the order of a
local equation when one reduced support has a regular principal ideal and
that equation does not vanish identically on the other support. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Pointwise

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions

theorem intersectionMultiplicity_eq_order (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B C : IrreducibleCloseds X.carrier)
    (hxA : IntersectionGeometry.supportPoint C ∈ (A : Set X.carrier)) (hxB : IntersectionGeometry.supportPoint C ∈ (B : Set X.carrier))
    (r : X.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C)) (hr : r ≠ 0)
    (hB : RingHom.ker (SupportStalkModule.Constructions.supportStalkMap X.carrier B (IntersectionGeometry.supportPoint C) hxB).hom = Ideal.span {r})
    (hAr : SupportStalkModule.Constructions.supportStalkMap X.carrier A (IntersectionGeometry.supportPoint C) hxA r ≠ 0) :
    IntersectionGeometry.intersectionMultiplicity X A B C =
      (Ring.ord ((Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (IntersectionGeometry.supportPreimage A (IntersectionGeometry.supportPoint C) hxA))
        (SupportStalkModule.Constructions.supportStalkMap X.carrier A (IntersectionGeometry.supportPoint C) hxA r)).toNat := by
  let R := X.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C)
  let S := (Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (IntersectionGeometry.supportPreimage A (IntersectionGeometry.supportPoint C) hxA)
  let T := (Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk (IntersectionGeometry.supportPreimage B (IntersectionGeometry.supportPoint C) hxB)
  let σ := SupportStalkModule.Constructions.supportStalkMap X.carrier A (IntersectionGeometry.supportPoint C) hxA
  let τ := SupportStalkModule.Constructions.supportStalkMap X.carrier B (IntersectionGeometry.supportPoint C) hxB
  let : Algebra R S := σ.hom.toAlgebra
  let : Algebra R T := τ.hom.toAlgebra
  let : IsDomain R := X.stalk_isDomain (IntersectionGeometry.supportPoint C)
  have hσ : Function.Surjective (algebraMap R S) := SupportStalkModule.Constructions.supportStalkMap_surjective X.carrier A _ hxA
  have hτ : Function.Surjective (Algebra.ofId R T) := SupportStalkModule.Constructions.supportStalkMap_surjective X.carrier B _ hxB
  have hI : RingHom.ker (Algebra.ofId R T) = r • (⊤ : Submodule R R) := by
    change RingHom.ker τ.hom = _
    rw [hB, ← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  let e : IntersectionGeometry.localSupportModule X.carrier B (IntersectionGeometry.supportPoint C) hxB ≃ₗ[R] QuotSMulTop r R :=
    (Ideal.quotientKerAlgEquivOfSurjective hτ).symm.toLinearEquiv.trans
      (Submodule.quotEquivOfEq _ _ hI)
  have hr' : IsSMulRegular R r := fun _ _ h => mul_left_cancel₀ hr h
  rw [IntersectionGeometry.intersectionMultiplicity, dite_eq_left ⟨hxA, hxB⟩]
  exact TorAlgebra.PrincipalIntersectionOrder.euler_eq_order_of_equiv R S hσ r hr' hAr
    (IntersectionGeometry.localSupportModule X.carrier B (IntersectionGeometry.supportPoint C) hxB) e X.ambientDimension

theorem intersectionMultiplicity_eq_order_left (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B C : IrreducibleCloseds X.carrier)
    (hxA : IntersectionGeometry.supportPoint C ∈ (A : Set X.carrier)) (hxB : IntersectionGeometry.supportPoint C ∈ (B : Set X.carrier))
    (r : X.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C)) (hr : r ≠ 0)
    (hA : RingHom.ker (SupportStalkModule.Constructions.supportStalkMap X.carrier A (IntersectionGeometry.supportPoint C) hxA).hom = Ideal.span {r})
    (hBr : SupportStalkModule.Constructions.supportStalkMap X.carrier B (IntersectionGeometry.supportPoint C) hxB r ≠ 0) :
    IntersectionGeometry.intersectionMultiplicity X A B C =
      (Ring.ord ((Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk (IntersectionGeometry.supportPreimage B (IntersectionGeometry.supportPoint C) hxB))
        (SupportStalkModule.Constructions.supportStalkMap X.carrier B (IntersectionGeometry.supportPoint C) hxB r)).toNat := by
  rw [Intersection.Symmetry.Constructions.intersectionMultiplicity_comm X A B C]
  exact intersectionMultiplicity_eq_order X B A C hxB hxA r hr hA hBr

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.PrincipalIntersection
