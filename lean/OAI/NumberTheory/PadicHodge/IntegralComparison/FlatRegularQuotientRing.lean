import OAI.NumberTheory.PadicHodge.IntegralComparison.FlatScalarExactness
import OAI.NumberTheory.PadicHodge.IntegralComparison.RegularQuotientScalarExactness
import Mathlib.RingTheory.RingHom.Flat

/-! # Flat Regular Quotient Ring -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FlatRegularQuotientRing

noncomputable section

/-! Scalar kernel exactness in a flat algebra over a regular prime-power quotient. -/

universe u v

variable (R : Type u) [CommRing R] (r : R) (hr : IsSMulRegular R r) (n : ℕ)
  (A : Type v) [CommRing A]
  (f : RegularQuotientScalarExactness.Ring R r n →+* A) (hf : f.Flat)

include hr hf in
theorem exact (x : A) : f (RegularQuotientScalarExactness.scalar R r n) * x = 0 ↔
    ∃ y : A, f (RegularQuotientScalarExactness.scalar R r n) ^ n * y = x := by
  let S := RegularQuotientScalarExactness.Ring R r n
  let : Algebra S A := f.toAlgebra
  let : Module.Flat S A := hf
  have h := FlatScalarExactness.exact S A
    (RegularQuotientScalarExactness.scalar R r n ^ n)
    (RegularQuotientScalarExactness.scalar R r n)
    (RegularQuotientScalarExactness.exact R r hr n) x
  change f (RegularQuotientScalarExactness.scalar R r n) * x = 0 ↔
    ∃ y, f (RegularQuotientScalarExactness.scalar R r n ^ n) * y = x at h
  exact (show f (RegularQuotientScalarExactness.scalar R r n ^ n) =
    f (RegularQuotientScalarExactness.scalar R r n) ^ n from map_pow f _ _ ) ▸ h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FlatRegularQuotientRing
