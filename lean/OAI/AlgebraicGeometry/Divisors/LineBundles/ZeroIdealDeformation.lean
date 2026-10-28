import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiber

/-! # Zero Ideal Deformation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ZeroIdealDeformation.BundleCycles

noncomputable section

/-! Deformation along the zero ideal is the actual polynomial algebra.
This identifies the constant family over the center inside a deformation. -/

open scoped BigOperators

variable (R : Type) [CommRing R]

theorem zeroDeformation_coefficient_negative (a : Deformation.Iff.BundleCycles.deformationAlgebra (⊥ : Ideal R))
    (n : ℤ) (hn : n < 0) : a.val.coeff n = 0 := by
  have he : (-n).toNat ≠ 0 := by omega
  have h := a.property n
  simpa only [Ideal.bot_pow he, Ideal.mem_bot] using h

theorem polynomialToZeroDeformation_bijective :
    Function.Bijective (GenericFiber.BundleCycles.polynomialToDeformation (⊥ : Ideal R)) := by
  classical
  constructor
  · intro a b h
    exact Polynomial.toLaurent_injective (congrArg Subtype.val h)
  · intro a
    refine ⟨∑ n ∈ a.val.coeff.support, Polynomial.monomial n.toNat (a.val.coeff n), Subtype.ext ?_⟩
    change Polynomial.toLaurent (∑ n ∈ a.val.coeff.support,
      Polynomial.monomial n.toNat (a.val.coeff n)) = a.val
    rw [map_sum]
    calc
      _ = ∑ n ∈ a.val.coeff.support, AddMonoidAlgebra.single n (a.val.coeff n) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn' : 0 ≤ n := by
          by_contra h
          exact (Finsupp.mem_support_iff.mp hn)
            (zeroDeformation_coefficient_negative R a n (lt_of_not_ge h))
        rw [Polynomial.toLaurent_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
          Int.toNat_of_nonneg hn']
      _ = a.val := AddMonoidAlgebra.sum_coeff_single a.val

def zeroDeformationEquiv : Polynomial R ≃ₐ[R] Deformation.Iff.BundleCycles.deformationAlgebra (⊥ : Ideal R) :=
  AlgEquiv.ofBijective (GenericFiber.BundleCycles.polynomialToDeformation (⊥ : Ideal R)) (polynomialToZeroDeformation_bijective R)

theorem zeroDeformationEquiv_X : zeroDeformationEquiv R Polynomial.X = Deformation.Iff.BundleCycles.deformationParameter (⊥ : Ideal R) :=
  GenericFiber.BundleCycles.polynomialToDeformation_X (⊥ : Ideal R)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ZeroIdealDeformation.BundleCycles
