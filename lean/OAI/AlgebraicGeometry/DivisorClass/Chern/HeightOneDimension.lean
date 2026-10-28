import OAI.AlgebraicGeometry.DivisorClass.Chern.PolynomialDimension
import Mathlib.RingTheory.IntegralClosure.GoingDown

/-! # Height One Dimension -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HeightOneDimension.Construction

noncomputable section

/-!
# ChernClass: height-one primes have transcendence codimension one

Noether normalization and going down reduce the statement to polynomial rings.
The quotient integral embedding preserves its actual Krull dimension, giving
the exact one-dimensional drop and then the transcendence-degree formula.
-/

variable (K A : Type) [Field K] [CommRing A] [IsDomain A]
variable [Algebra K A] [Algebra.FiniteType K A]

include K in
/-- A height-one prime in a finite-type domain lowers Krull dimension by exactly one. -/
theorem finiteType_height_one_quotient_dimension (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    ringKrullDim (A ⧸ p) + 1 = ringKrullDim A := by
  obtain ⟨n, f, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let P := MvPolynomial (Fin n) K
  let : Algebra P A := f.toRingHom.toAlgebra
  let : Algebra.IsIntegral P A := ⟨hint⟩
  let : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  let q : Ideal P := p.comap (algebraMap P A)
  have hq : q.height = 1 := by
    have h := IntegralDimension.Construction.integral_comap_height (R := P) (S := A) ⟨p, inferInstance⟩
    have h' : p.height = q.height := by
      rw [← PrimeSpectrum.height_eq_orderHeight, ← PrimeSpectrum.height_eq_orderHeight] at h
      exact h
    exact h'.symm.trans hp
  have hquot : ringKrullDim (A ⧸ p) = ringKrullDim (P ⧸ q) :=
    IntegralDimension.Construction.integral_ringKrullDim_eq (R := P ⧸ q) (S := A ⧸ p) Ideal.algebraMap_quotient_injective
  calc
    ringKrullDim (A ⧸ p) + 1 = ringKrullDim (P ⧸ q) + 1 := congrArg (fun d => d + 1) hquot
    _ = ringKrullDim P := PolynomialDimension.Construction.mvPolynomial_height_one_quotient_dimension K n q hq
    _ = ringKrullDim A := (IntegralDimension.Construction.integral_ringKrullDim_eq (R := P) (S := A) hinj).symm

/-- The same height-one statement in the actual transcendence-degree grading. -/
theorem finiteType_height_one_trdeg (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    (Algebra.trdeg K (A ⧸ p)).toNat + 1 = (Algebra.trdeg K A).toNat := by
  have h := finiteType_height_one_quotient_dimension K A p hp
  rw [FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg K (A ⧸ p), FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg K A] at h
  exact_mod_cast h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HeightOneDimension.Construction
