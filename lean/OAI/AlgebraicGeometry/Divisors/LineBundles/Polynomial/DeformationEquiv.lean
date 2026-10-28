import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.CoordinateDeformation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.RegularParameterInjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiber

/-! # Deformation Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.DeformationEquiv.BundleCycles

noncomputable section

section

/-! The deformation of the coordinate origin has an actual polynomial
model. Its variables are x/t and its final variable is the parameter t. -/

variable (A ι : Type) [CommRing A]

def polynomialDeformationModel : Polynomial (MvPolynomial ι A) →+*
    Deformation.Iff.BundleCycles.deformationAlgebra (MvPolynomial.idealOfVars ι A) :=
  Polynomial.eval₂RingHom CoordinateDeformation.BundleCycles.polynomialCoordinateDeformationMap (Deformation.Iff.BundleCycles.deformationParameter (MvPolynomial.idealOfVars ι A))

theorem polynomialDeformationModel_injective : Function.Injective (polynomialDeformationModel A ι) := by
  apply RegularParameterInjection.BundleCycles.polynomialEval_injective_of_regular_parameter CoordinateDeformation.BundleCycles.polynomialCoordinateDeformationMap
    (Deformation.Iff.BundleCycles.deformationParameter (MvPolynomial.idealOfVars ι A)) (Deformation.Iff.BundleCycles.deformationSpecialIdeal (MvPolynomial.idealOfVars ι A))
    (Ideal.subset_span rfl) (Deformation.Iff.BundleCycles.deformationParameter_regular _)
  rw [CoordinateDeformation.BundleCycles.polynomialCoordinateDeformationMap_mod_parameter]
  exact (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv (MvPolynomial.idealOfVars ι A)).injective.comp CoordinateCone.BundleCycles.polynomialCoordinateConeMap_injective

theorem polynomialDeformationModel_monomial_val (n : ℕ) (d : ι →₀ ℕ) (a : A) :
    (polynomialDeformationModel A ι (Polynomial.monomial n (MvPolynomial.monomial d a))).val =
      AddMonoidAlgebra.single ((n : ℤ) - d.degree) (MvPolynomial.monomial d a) := by
  change ((Polynomial.monomial n (MvPolynomial.monomial d a)).eval₂
    CoordinateDeformation.BundleCycles.polynomialCoordinateDeformationMap (Deformation.Iff.BundleCycles.deformationParameter (MvPolynomial.idealOfVars ι A))).val = _
  rw [Polynomial.eval₂_monomial]
  change (CoordinateDeformation.BundleCycles.polynomialCoordinateDeformationMap (MvPolynomial.monomial d a)).val *
    ((Deformation.Iff.BundleCycles.deformationParameter (MvPolynomial.idealOfVars ι A)) ^ n).val = _
  rw [CoordinateDeformation.BundleCycles.polynomialCoordinateDeformationMap_monomial_val, GenericFiber.BundleCycles.deformationParameter_pow_val]
  change AddMonoidAlgebra.single (-(d.degree : ℤ)) (MvPolynomial.monomial d a) *
    AddMonoidAlgebra.single (n : ℤ) 1 = _
  rw [AddMonoidAlgebra.single_mul_single, mul_one]
  congr 1
  omega

def polynomialDeformationModelLaurent : Polynomial (MvPolynomial ι A) →+* LaurentPolynomial (MvPolynomial ι A) :=
  (Deformation.Iff.BundleCycles.deformationAlgebra (MvPolynomial.idealOfVars ι A)).val.toRingHom.comp (polynomialDeformationModel A ι)

end

/-! Every element of the coordinate-origin deformation has a unique
polynomial expression in x/t and t, over an arbitrary coefficient ring. -/

open scoped BigOperators

variable (A ι : Type) [CommRing A]

theorem polynomialDeformationModel_single_mem_range (n : ℤ) (q : MvPolynomial ι A)
    (hq : q ∈ MvPolynomial.idealOfVars ι A ^ (-n).toNat) :
    AddMonoidAlgebra.single n q ∈ (polynomialDeformationModelLaurent A ι).rangeS := by
  classical
  have he := congrArg (AddMonoidAlgebra.lsingle (R := MvPolynomial ι A) n) q.as_sum
  rw [map_sum] at he
  change AddMonoidAlgebra.single n q =
    ∑ d ∈ q.support, AddMonoidAlgebra.single n (MvPolynomial.monomial d (q.coeff d)) at he
  rw [he]
  apply Subsemiring.sum_mem
  intro d hd
  have hdegree := (MvPolynomial.mem_pow_idealOfVars_iff (-n).toNat q).mp hq d hd
  have hk : 0 ≤ n + (d.degree : ℤ) := by omega
  have hkn : (((n + (d.degree : ℤ)).toNat : ℕ) : ℤ) - d.degree = n := by
    rw [Int.toNat_of_nonneg hk]
    omega
  refine ⟨Polynomial.monomial (n + (d.degree : ℤ)).toNat (MvPolynomial.monomial d (q.coeff d)), ?_⟩
  change (polynomialDeformationModel A ι
    (Polynomial.monomial (n + (d.degree : ℤ)).toNat (MvPolynomial.monomial d (q.coeff d)))).val = _
  rw [polynomialDeformationModel_monomial_val, hkn]

theorem polynomialDeformationModel_surjective : Function.Surjective (polynomialDeformationModel A ι) := by
  classical
  intro a
  have ha : a.val ∈ (polynomialDeformationModelLaurent A ι).rangeS := by
    rw [← AddMonoidAlgebra.sum_coeff_single a.val]
    exact Subsemiring.sum_mem _ (fun n _ => polynomialDeformationModel_single_mem_range A ι n _ (a.property n))
  obtain ⟨b, hb⟩ := ha
  exact ⟨b, Subtype.ext hb⟩

def polynomialDeformationEquiv : Polynomial (MvPolynomial ι A) ≃+*
    Deformation.Iff.BundleCycles.deformationAlgebra (MvPolynomial.idealOfVars ι A) :=
  RingEquiv.ofBijective (polynomialDeformationModel A ι)
    ⟨polynomialDeformationModel_injective A ι, polynomialDeformationModel_surjective A ι⟩

theorem polynomialDeformationEquiv_parameter :
    polynomialDeformationEquiv A ι Polynomial.X = Deformation.Iff.BundleCycles.deformationParameter (MvPolynomial.idealOfVars ι A) :=
  Polynomial.eval₂_X _ _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.DeformationEquiv.BundleCycles
