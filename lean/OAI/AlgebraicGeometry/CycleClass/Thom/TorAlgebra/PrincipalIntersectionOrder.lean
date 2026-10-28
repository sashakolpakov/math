import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Principal
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! # Principal Intersection Order -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.PrincipalIntersectionOrder

noncomputable section

/-! Intersection against a regular principal quotient has the actual
order of vanishing on an integral closed local subscheme. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

theorem quotient_length (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (hA : Function.Surjective (algebraMap R A)) (r : R) :
    Module.length R (QuotSMulTop r A) = Ring.ord A (algebraMap R A r) := by
  rw [(QuotSMulTop.equivTensorQuot r A).length_eq,
    ← ((Ideal.qoutMapEquivTensorQout (R := R) (I := Ideal.span {r}) A).restrictScalars R).length_eq,
    Module.length_eq_of_surjective (M := A ⧸ (Ideal.span {r}).map (algebraMap R A)) hA,
    Ideal.map_span, Set.image_singleton]
  rfl

theorem euler_eq_order (R A : Type u) [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
    (hA : Function.Surjective (algebraMap R A)) (r : R) (hr : IsSMulRegular R r)
    (hra : algebraMap R A r ≠ 0) (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (Module.length R (((Tor (ModuleCat R) i).obj (ModuleCat.of R A)).obj
        (ModuleCat.of R (QuotSMulTop r R)))).toNat) =
      (Ring.ord A (algebraMap R A r)).toNat := by
  have hm : IsSMulRegular (ModuleCat.of R A) r := by
    intro x y h
    apply mul_left_cancel₀ hra
    change r • (x : A) = r • (y : A) at h
    simpa only [Algebra.smul_def] using h
  rw [Principal.Tor.euler_length R r hr (.of R A) hm, quotient_length R A hA r]

theorem euler_eq_order_of_equiv (R A : Type u) [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] (hA : Function.Surjective (algebraMap R A)) (r : R)
    (hr : IsSMulRegular R r) (hra : algebraMap R A r ≠ 0) (N : ModuleCat.{u} R)
    (e : N ≃ₗ[R] QuotSMulTop r R) (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (Module.length R (((Tor (ModuleCat R) i).obj (ModuleCat.of R A)).obj N)).toNat) =
      (Ring.ord A (algebraMap R A r)).toNat := by
  have hlen (i : ℕ) :
      Module.length R (((Tor (ModuleCat R) i).obj (.of R A)).obj N) =
      Module.length R (((Tor (ModuleCat R) i).obj (.of R A)).obj (.of R (QuotSMulTop r R))) :=
    ((((Tor (ModuleCat R) i).obj (.of R A)).mapIso e.toModuleIso).toLinearEquiv).length_eq
  simp_rw [hlen]
  exact euler_eq_order R A hA r hr hra d

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.PrincipalIntersectionOrder
