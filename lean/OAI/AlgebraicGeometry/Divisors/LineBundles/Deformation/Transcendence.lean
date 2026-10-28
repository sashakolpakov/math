import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FiniteType
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! # Transcendence -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Transcendence.BundleCycles

noncomputable section

/-!
# LineBundleCycles: transcendence degree of the deformation algebra

Both the polynomial ring and the extended-Rees algebra localize to the
same Laurent ring. These faithful algebraic extensions show that the
deformation adds exactly one transcendental parameter.
-/

universe u
variable (R : Type u) [CommRing R] [IsDomain R]

/-- Laurent polynomials have exactly one transcendental parameter over their coefficient domain. -/
theorem laurentPolynomial_trdeg : Algebra.trdeg R (LaurentPolynomial R) = 1 := by
  let : IsScalarTower R (Polynomial R) (LaurentPolynomial R) :=
    IsScalarTower.of_algebraMap_eq (fun r => (Polynomial.toLaurent_C r).symm)
  let : FaithfulSMul (Polynomial R) (LaurentPolynomial R) :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial R) (LaurentPolynomial R)).mpr
      Polynomial.toLaurent_injective
  let : Algebra.IsAlgebraic (Polynomial R) (LaurentPolynomial R) :=
    IsLocalization.isAlgebraic (LaurentPolynomial R) (Submonoid.powers (Polynomial.X : Polynomial R))
  have h := trdeg_add_eq R (Polynomial R) (A := LaurentPolynomial R)
  simp only [Polynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero] at h
  exact h.symm

variable {R} (I : Ideal R)

/-- The extended-Rees algebra adds precisely one transcendental parameter. -/
theorem deformationAlgebra_trdeg : Algebra.trdeg R (Iff.BundleCycles.deformationAlgebra I) = 1 := by
  let : Algebra.IsAlgebraic (Iff.BundleCycles.deformationAlgebra I) (LaurentPolynomial R) :=
    IsLocalization.isAlgebraic (LaurentPolynomial R) (Submonoid.powers (Iff.BundleCycles.deformationParameter I))
  have h := trdeg_add_eq R (Iff.BundleCycles.deformationAlgebra I) (A := LaurentPolynomial R)
  simp only [trdeg_eq_zero, add_zero] at h
  exact h.trans (laurentPolynomial_trdeg R)

variable (k : Type u) [Field k] [Algebra k R]

/-- The coefficient-field action on the deformation is induced by the actual constants map. -/
abbrev deformationScalarAlgebra : Algebra k (Iff.BundleCycles.deformationAlgebra I) :=
  Algebra.compHom (Iff.BundleCycles.deformationAlgebra I) (algebraMap k R)

omit [IsDomain R] in
theorem deformationScalar_isScalarTower :
    letI := deformationScalarAlgebra I k
    IsScalarTower k R (Iff.BundleCycles.deformationAlgebra I) := by
  let := deformationScalarAlgebra I k
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Over the original coefficient field, the actual deformation adds one to transcendence degree. -/
theorem deformationAlgebra_trdeg_base :
    letI := deformationScalarAlgebra I k
    Algebra.trdeg k (Iff.BundleCycles.deformationAlgebra I) = Algebra.trdeg k R + 1 := by
  let := deformationScalarAlgebra I k
  have : IsScalarTower k R (Iff.BundleCycles.deformationAlgebra I) := deformationScalar_isScalarTower I k
  have h := trdeg_add_eq k R (A := Iff.BundleCycles.deformationAlgebra I)
  rw [deformationAlgebra_trdeg I] at h
  exact h.symm

/-- Finite type makes the same formula exact in the natural-number dimension grading. -/
theorem deformationAlgebra_trdeg_toNat [Algebra.FiniteType k R] :
    letI := deformationScalarAlgebra I k
    (Algebra.trdeg k (Iff.BundleCycles.deformationAlgebra I)).toNat = (Algebra.trdeg k R).toNat + 1 := by
  let := deformationScalarAlgebra I k
  have hfin : Algebra.trdeg k R < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  rw [deformationAlgebra_trdeg_base I k, Cardinal.toNat_add hfin (by simp)]
  simp

omit [IsDomain R] in
/-- Finite-type coefficients and a finitely generated center give a finite-type deformation over the field. -/
theorem deformationAlgebra_finiteType_base [Algebra.FiniteType k R] (hI : I.FG) :
    letI := deformationScalarAlgebra I k
    Algebra.FiniteType k (Iff.BundleCycles.deformationAlgebra I) := by
  let := deformationScalarAlgebra I k
  have : IsScalarTower k R (Iff.BundleCycles.deformationAlgebra I) := deformationScalar_isScalarTower I k
  have : Algebra.FiniteType R (Iff.BundleCycles.deformationAlgebra I) := Deformation.FiniteType.BundleCycles.deformationAlgebra_finiteType I hI
  exact Algebra.FiniteType.trans (S := R) inferInstance inferInstance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Transcendence.BundleCycles
