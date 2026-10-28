import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Iff

/-! # Generic Fiber -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiber.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the punctured affine deformation

Inverting the deformation parameter identifies R[t,I/t][t⁻¹] with
R[t,t⁻¹]. The proof clears negative exponents of an arbitrary Laurent
polynomial, so the identification applies to every ideal in every base ring.
-/

open LaurentPolynomial

universe u
variable {R : Type u} [CommRing R]

/-- Ordinary polynomials belong to the extended Rees algebra. -/
theorem polynomial_mem_deformationAlgebra (I : Ideal R) (p : Polynomial R) :
    p.toLaurent ∈ Deformation.Iff.BundleCycles.deformationAlgebra I := by
  intro n
  by_cases hn : n < 0
  · rw [Deformation.Iff.BundleCycles.toLaurent_coeff_neg p n hn]
    exact Ideal.zero_mem _
  · have he : (-n).toNat = 0 := by omega
    simp [he]

/-- Inclusion of the parameter polynomial ring into the deformation. -/
def polynomialToDeformation (I : Ideal R) : Polynomial R →ₐ[R] Deformation.Iff.BundleCycles.deformationAlgebra I :=
  Polynomial.toLaurentAlg.codRestrict (Deformation.Iff.BundleCycles.deformationAlgebra I)
    (polynomial_mem_deformationAlgebra I)

@[simp]
theorem polynomialToDeformation_val (I : Ideal R) (p : Polynomial R) :
    (polynomialToDeformation I p).val = p.toLaurent := rfl

@[simp]
theorem polynomialToDeformation_X (I : Ideal R) :
    polynomialToDeformation I Polynomial.X = Deformation.Iff.BundleCycles.deformationParameter I := by
  apply Subtype.ext
  exact Polynomial.toLaurent_X

theorem deformationParameter_pow_val (I : Ideal R) (n : ℕ) :
    ((Deformation.Iff.BundleCycles.deformationParameter I ^ n : Deformation.Iff.BundleCycles.deformationAlgebra I) : LaurentPolynomial R) = T (n : ℤ) := by
  change (T 1 : LaurentPolynomial R) ^ n = _
  rw [T_pow, mul_one]

/-- Laurent polynomials are precisely the localization of the deformation
algebra away from its regular parameter. -/
instance deformation_isLocalization (I : Ideal R) :
    IsLocalization.Away (Deformation.Iff.BundleCycles.deformationParameter I) (LaurentPolynomial R) where
  map_units := by
    rintro ⟨p, ⟨n, rfl⟩⟩
    change IsUnit ((Deformation.Iff.BundleCycles.deformationParameter I ^ n : Deformation.Iff.BundleCycles.deformationAlgebra I) : LaurentPolynomial R)
    rw [deformationParameter_pow_val]
    exact isUnit_T _
  surj p := by
    obtain ⟨n, q, hq⟩ := exists_T_pow p
    refine ⟨(polynomialToDeformation I q,
      ⟨Deformation.Iff.BundleCycles.deformationParameter I ^ n, ⟨n, rfl⟩⟩), ?_⟩
    change p * ((Deformation.Iff.BundleCycles.deformationParameter I ^ n : Deformation.Iff.BundleCycles.deformationAlgebra I) : LaurentPolynomial R) =
      (polynomialToDeformation I q).val
    rw [deformationParameter_pow_val, polynomialToDeformation_val, hq]
  exists_of_eq := by
    intro p q hpq
    have he : p = q := Subtype.ext hpq
    exact ⟨1, by rw [he]⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiber.BundleCycles
