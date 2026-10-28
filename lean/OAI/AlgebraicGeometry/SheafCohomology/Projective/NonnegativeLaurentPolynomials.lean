import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! # Nonnegative Laurent Polynomials -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! Nonnegative homogeneous Laurent weights are ordinary polynomial monomials. -/

open _root_.AlgebraicGeometry
universe u
variable {σ : Type} [Fintype σ]

def nonnegativeLaurentWeightEquivDegree (n : ℕ) :
    LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (n : ℤ) ≃ {a : σ →₀ ℕ // Finsupp.degree a = n} where
  toFun e := ⟨e.val.val.mapRange Int.toNat (by rfl), by
    have hcast (i : σ) : ((e.val.val i).toNat : ℤ) = e.val.val i := by
      have := e.property i
      omega
    have hdeg : ((Finsupp.degree (e.val.val.mapRange Int.toNat (by rfl)) : ℕ) : ℤ) = (n : ℤ) := by
      rw [Finsupp.degree_eq_sum, Nat.cast_sum]
      simp only [Finsupp.mapRange_apply, hcast]
      rw [← Finsupp.degree_eq_sum]
      exact e.val.property
    exact_mod_cast hdeg⟩
  invFun a := ⟨⟨a.val.mapRange (fun k : ℕ => (k : ℤ)) (by rfl), by
    rw [Finsupp.degree_eq_sum]
    simp only [Finsupp.mapRange_apply, ← Nat.cast_sum]
    rw [← Finsupp.degree_eq_sum, a.property]⟩,
    fun i => by change (0 : ℤ) ≤ (a.val i : ℤ); exact Int.natCast_nonneg _⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    change ((e.val.val i).toNat : ℤ) = e.val.val i
    have := e.property i
    omega
  right_inv a := by
    apply Subtype.ext
    ext i
    change (a.val i : ℤ).toNat = a.val i
    omega

def homogeneousPolynomialCoefficientsEquiv (R : Type u) [CommRing R] (n : ℕ) :
    homogeneousSubmodule σ R n ≃ₗ[R] (LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (n : ℤ) → R) :=
  (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported σ R n)).trans
    ((AddMonoidAlgebra.supportedEquivFinsupp {a : σ →₀ ℕ | a.degree = n}).trans
      ((Finsupp.domLCongr (nonnegativeLaurentWeightEquivDegree n).symm).trans
        (Finsupp.linearEquivFunOnFinite R R _)))

def laurentZeroCyclesEquivPolynomials (R : Type u) [CommRing R] [LinearOrder σ]
    (j : σ) (n : ℕ) :
    LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) (n : ℤ) ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
      homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) n :=
  (LaurentZeroCoefficients.MvPolynomial.laurentZeroCyclesEquivCoefficients (R := R) (n : ℤ) (Int.natCast_nonneg n) j).trans
    (homogeneousPolynomialCoefficientsEquiv _ n).symm

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial
