import OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralDimension
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! # Finite Type Dimension -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.FiniteTypeDimension.Construction

noncomputable section

/-!
# ChernClass: finite-type integral algebras have their function-field dimension

Noether normalization identifies both Krull dimension and transcendence degree
with the number of polynomial parameters, using the actual integral embedding.
-/

variable (K A : Type) [Field K] [CommRing A] [IsDomain A]
variable [Algebra K A] [Algebra.FiniteType K A]

/-- Krull dimension agrees with the finite transcendence degree of a finite-type domain. -/
theorem finiteType_ringKrullDim_eq_trdeg :
    ringKrullDim A = ((Algebra.trdeg K A).toNat : WithBot ℕ∞) := by
  obtain ⟨n, f, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let P := MvPolynomial (Fin n) K
  let : Algebra P A := f.toRingHom.toAlgebra
  let : Algebra.IsIntegral P A := ⟨hint⟩
  let : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  let : IsScalarTower K P A := IsScalarTower.of_algebraMap_eq' (by
    ext k
    exact (f.commutes k).symm)
  have hd : ringKrullDim A = (n : WithBot ℕ∞) := by
    rw [IntegralDimension.Construction.integral_ringKrullDim_eq (R := P) (S := A) hinj]
    change ringKrullDim (MvPolynomial (Fin n) K) = _
    simp
  have ht : (n : Cardinal) = Algebra.trdeg K A := by
    have h := trdeg_add_eq K P (A := A)
    rw [trdeg_eq_zero (R := P) (A := A), add_zero] at h
    change Algebra.trdeg K (MvPolynomial (Fin n) K) = _ at h
    simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin, Cardinal.lift_natCast] using h
  rw [hd, ← ht, Cardinal.toNat_natCast]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.FiniteTypeDimension.Construction
