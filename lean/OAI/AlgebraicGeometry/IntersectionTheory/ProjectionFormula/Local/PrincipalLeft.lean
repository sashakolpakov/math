import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.TorLeft

/-! # Principal Left -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.PrincipalLeft

noncomputable section

/-! ThomClass's exact native intersection multiplicity equals the order of a
local equation when one reduced support has a regular principal ideal and
that equation does not vanish identically on the other support. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Pointwise

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

universe u

theorem euler_eq_order (R A : Type u) [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] (hA : Function.Surjective (algebraMap R A)) (r : R)
    (hr : IsSMulRegular R r) (hra : algebraMap R A r ≠ 0) (N : ModuleCat.{u} R)
    (e : N ≃ₗ[R] QuotSMulTop r R) (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (Module.length R (((Tor (ModuleCat R) i).obj N).obj (ModuleCat.of R A))).toNat) =
      (Ring.ord A (algebraMap R A r)).toNat := by
  have hlen (i : ℕ) :
      Module.length R (((Tor (ModuleCat R) i).obj N).obj (.of R A)) =
      Module.length R (((Tor (ModuleCat R) i).obj (.of R (QuotSMulTop r R))).obj (.of R A)) :=
    ((((Tor (ModuleCat R) i).flip.obj (.of R A)).mapIso e.toModuleIso).toLinearEquiv).length_eq
  simp_rw [hlen]
  have hm : IsSMulRegular (ModuleCat.of R A) r := by
    intro x y h
    apply mul_left_cancel₀ hra
    change r • (x : A) = r • (y : A) at h
    simpa only [Algebra.smul_def] using h
  rw [Principal.TorLeft.euler_length R r hr (.of R A) hm,
    Principal.Order.quotient_length R A hA r]

theorem intersectionMultiplicity_eq_order (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B C : IrreducibleCloseds X.carrier)
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (A : Set X.carrier)) (hxB : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (B : Set X.carrier))
    (r : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C)) (hr : r ≠ 0)
    (hB : RingHom.ker (Principal.supportStalkMap X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxB).hom = Ideal.span {r})
    (hAr : Principal.supportStalkMap X.carrier A (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxA r ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B A C =
      (Ring.ord ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxA))
        (Principal.supportStalkMap X.carrier A (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxA r)).toNat := by
  let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C)
  let S := (CycleClass.Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxA)
  let T := (CycleClass.Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage B (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxB)
  let σ := Principal.supportStalkMap X.carrier A (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxA
  let τ := Principal.supportStalkMap X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxB
  let : Algebra R S := σ.hom.toAlgebra
  let : Algebra R T := τ.hom.toAlgebra
  let : IsDomain R := X.stalk_isDomain (CycleClass.Thom.IntersectionGeometry.supportPoint C)
  have hσ : Function.Surjective (algebraMap R S) := Principal.supportStalkMap_surjective X.carrier A _ hxA
  have hτ : Function.Surjective (Algebra.ofId R T) := Principal.supportStalkMap_surjective X.carrier B _ hxB
  have hI : RingHom.ker (Algebra.ofId R T) = r • (⊤ : Submodule R R) := by
    change RingHom.ker τ.hom = _
    rw [hB, ← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  let e : CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxB ≃ₗ[R] QuotSMulTop r R :=
    (Ideal.quotientKerAlgEquivOfSurjective hτ).symm.toLinearEquiv.trans
      (Submodule.quotEquivOfEq _ _ hI)
  have hr' : IsSMulRegular R r := fun _ _ h => mul_left_cancel₀ hr h
  rw [CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_left ⟨hxB, hxA⟩]
  exact euler_eq_order R S hσ r hr' hAr
    (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxB) e X.ambientDimension

theorem intersectionMultiplicity_comm_of_principal (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B C : IrreducibleCloseds X.carrier)
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (A : Set X.carrier)) (hxB : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (B : Set X.carrier))
    (r : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C)) (hr : r ≠ 0)
    (hB : RingHom.ker (Principal.supportStalkMap X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxB).hom = Ideal.span {r})
    (hAr : Principal.supportStalkMap X.carrier A (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxA r ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A B C = CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B A C :=
  (Principal.intersectionMultiplicity_eq_order X A B C hxA hxB r hr hB hAr).trans
    (intersectionMultiplicity_eq_order X A B C hxA hxB r hr hB hAr).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.PrincipalLeft
