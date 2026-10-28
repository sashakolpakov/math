import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CokernelLength
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.LocalRing.Length

/-! # Length -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Length

noncomputable section

/-!
# ProjectionFormula: divisor lengths under finite birational enlargement

This module compares the actual quotient lengths before and after an
injective finite-colength extension. The base ring need not be normal.
-/

open LinearMap _root_.Submodule

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem range_mul (a : S) :
    (LinearMap.mul R S a).range = (Ideal.span {a}).restrictScalars R := by
  ext b
  change (∃ x, a * x = b) ↔ b ∈ Ideal.span {a}
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx.symm⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hx.symm⟩

def mulCokernelEquiv (a : S) :
    (S ⧸ (LinearMap.mul R S a).range) ≃ₗ[R] S ⧸ Ideal.span {a} :=
  (Submodule.quotEquivOfEq _ _ (range_mul (R := R) a)).trans
    (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {a}))

/-- Restricted quotient length is additive on multiplication by nonzero
elements, even when the extension ring has several maximal ideals. -/
theorem length_quotient_mul [IsDomain S] (a b : S) (hb : b ≠ 0) :
    Module.length R (S ⧸ Ideal.span {a * b}) =
      Module.length R (S ⧸ Ideal.span {a}) + Module.length R (S ⧸ Ideal.span {b}) := by
  have hcomp : (LinearMap.mul R S b).comp (LinearMap.mul R S a) =
      LinearMap.mul R S (a * b) := by
    apply LinearMap.ext
    intro x
    exact (mul_left_comm b a x).trans (mul_assoc a b x).symm
  have h := CokernelLength.length_cokernel_comp
    (LinearMap.mul R S a) (LinearMap.mul R S b) (mul_right_injective₀ hb)
  rw [hcomp] at h
  rw [← (mulCokernelEquiv (R := R) (a * b)).length_eq,
    ← (mulCokernelEquiv (R := R) a).length_eq,
    ← (mulCokernelEquiv (R := R) b).length_eq]
  exact h

/-- Quotient-length comparison used for the normalization of a singular
one-dimensional local ring. The finite-colength condition is independent of
the element whose order is being computed. -/
theorem ord_eq_length_extension [IsDomain S]
    (hinj : Function.Injective (algebraMap R S))
    (hfinite : Module.length R (S ⧸ (Algebra.linearMap R S).range) ≠ ⊤)
    (a : R) (ha : algebraMap R S a ≠ 0) :
    Ring.ord R a = Module.length R (S ⧸ Ideal.span {algebraMap R S a}) := by
  have hcomm : (Algebra.linearMap R S).comp (LinearMap.mul R R a) =
      (LinearMap.mul R S (algebraMap R S a)).comp (Algebra.linearMap R S) := by
    apply LinearMap.ext
    intro x
    exact map_mul (algebraMap R S) a x
  have h := CokernelLength.length_cokernel_eq_of_finite_colength
    (Algebra.linearMap R S) (LinearMap.mul R R a)
    (LinearMap.mul R S (algebraMap R S a)) hinj (mul_right_injective₀ ha) hcomm hfinite
  exact (mulCokernelEquiv (R := R) a).length_eq.symm.trans
    (h.trans (mulCokernelEquiv (R := R) (algebraMap R S a)).length_eq)

/-- For one local branch, the comparison has exactly the residue-degree
weight of algebraic cycle pushforward. The source ring may be singular. -/
theorem ord_eq_residueDegree_mul_ord [IsDomain S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
    (hinj : Function.Injective (algebraMap R S))
    (hfinite : Module.length R (S ⧸ (Algebra.linearMap R S).range) ≠ ⊤)
    (a : R) (ha : algebraMap R S a ≠ 0) :
    Ring.ord R a =
      (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) : ℕ∞) *
        Ring.ord S (algebraMap R S a) := by
  rw [ord_eq_length_extension hinj hfinite a ha,
    IsLocalRing.length_restrictScalars R S (S ⧸ Ideal.span {algebraMap R S a}),
    Module.length_eq_finrank]
  exact mul_comm _ _

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Length
