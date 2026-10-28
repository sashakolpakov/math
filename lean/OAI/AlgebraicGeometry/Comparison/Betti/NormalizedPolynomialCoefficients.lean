import OAI.AlgebraicGeometry.Comparison.Betti.NegativeLaurentMonomialExponents
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! # Normalized Polynomial Coefficients -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.NormalizedPolynomialCoefficients.Dolbeault

noncomputable section

section

/-! Coefficients identify normalized homogeneous polynomials with the original finite Laurent weights. -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def positiveMonomialExponentSet (ι : Type) (k : ℕ) : Set (ι →₀ ℕ) :=
  {e | e.degree = k ∧ ∀ i, 0 < e i}

theorem normalizedPolynomial_coeff_supported_iff (k : ℕ) (P : MvPolynomial ι ℂ) :
    P ∈ NormalizedHomogeneousPolynomials.Dolbeault.normalizedHomogeneousPolynomials Finset.univ k ↔
      (AddMonoidAlgebra.coeffLinearEquiv ℂ) P ∈
        Finsupp.supported ℂ ℂ (positiveMonomialExponentSet ι k) := by
  rw [NormalizedPolynomialSupports.Dolbeault.normalizedHomogeneousPolynomials_mem_iff, Finsupp.mem_supported]
  constructor
  · rintro ⟨hP, hs⟩ e he
    refine ⟨?_, fun i => hs e he i (Finset.mem_univ i)⟩
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hP (MvPolynomial.mem_support_iff.mp he)
  · intro h
    refine ⟨?_, fun e he i _ => (h he).2 i⟩
    intro e he
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using (h (MvPolynomial.mem_support_iff.mpr he)).1

def normalizedPolynomialSupportedCoefficientEquiv (k : ℕ) :
    NormalizedHomogeneousPolynomials.Dolbeault.normalizedHomogeneousPolynomials (Finset.univ : Finset ι) k ≃ₗ[ℂ]
      Finsupp.supported ℂ ℂ (positiveMonomialExponentSet ι k) where
  toFun P := ⟨(AddMonoidAlgebra.coeffLinearEquiv ℂ) P.val,
    (normalizedPolynomial_coeff_supported_iff k P.val).mp P.property⟩
  invFun f := ⟨(AddMonoidAlgebra.coeffLinearEquiv ℂ).symm f.val,
    (normalizedPolynomial_coeff_supported_iff k _).mpr
      (by simpa only [LinearEquiv.apply_symm_apply] using f.property)⟩
  left_inv P := Subtype.ext ((AddMonoidAlgebra.coeffLinearEquiv ℂ).symm_apply_apply P.val)
  right_inv f := Subtype.ext ((AddMonoidAlgebra.coeffLinearEquiv ℂ).apply_symm_apply f.val)
  map_add' P Q := Subtype.ext ((AddMonoidAlgebra.coeffLinearEquiv ℂ).map_add P.val Q.val)
  map_smul' c P := Subtype.ext ((AddMonoidAlgebra.coeffLinearEquiv ℂ).map_smul c P.val)

def normalizedPolynomialPositiveCoefficientEquiv (k : ℕ) :
    NormalizedHomogeneousPolynomials.Dolbeault.normalizedHomogeneousPolynomials (Finset.univ : Finset ι) k ≃ₗ[ℂ]
      (NegativeLaurentMonomialExponents.Dolbeault.positiveMonomialExponent ι k →₀ ℂ) :=
  (normalizedPolynomialSupportedCoefficientEquiv k).trans
    (Finsupp.supportedEquivFinsupp (positiveMonomialExponentSet ι k))

theorem normalizedPolynomialPositiveCoefficientEquiv_apply (k : ℕ)
    (P : NormalizedHomogeneousPolynomials.Dolbeault.normalizedHomogeneousPolynomials (Finset.univ : Finset ι) k)
    (e : NegativeLaurentMonomialExponents.Dolbeault.positiveMonomialExponent ι k) :
    normalizedPolynomialPositiveCoefficientEquiv k P e = AddMonoidAlgebra.coeff (P.val) (e.val) := rfl

end

section

/-! Normalized polynomial coefficients in the original algebraic Laurent exponent indexing. -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem fullNegativeMonomialExponent_finite (k : ℕ) : Finite (NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent ι k) :=
  (SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_univ
    (σ := ι) (-(k : ℤ))).to_subtype

attribute [local instance] fullNegativeMonomialExponent_finite

def normalizedPolynomialNegativeCoefficientEquiv (k : ℕ) :
    NormalizedHomogeneousPolynomials.Dolbeault.normalizedHomogeneousPolynomials (Finset.univ : Finset ι) k ≃ₗ[ℂ]
      (NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent ι k → ℂ) :=
  (normalizedPolynomialPositiveCoefficientEquiv k).trans
    ((Finsupp.domLCongr (NegativeLaurentMonomialExponents.Dolbeault.negativeLaurentMonomialExponentEquiv k)).trans
      (Finsupp.linearEquivFunOnFinite ℂ ℂ (NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent ι k)))

theorem normalizedPolynomialNegativeCoefficientEquiv_apply (k : ℕ)
    (P : NormalizedHomogeneousPolynomials.Dolbeault.normalizedHomogeneousPolynomials (Finset.univ : Finset ι) k)
    (e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent ι k) :
    normalizedPolynomialNegativeCoefficientEquiv k P e =
      AddMonoidAlgebra.coeff (P.val) ((NegativeLaurentMonomialExponents.Dolbeault.negativeToPositiveMonomialExponent k e).val) := rfl

theorem normalizedPolynomialNegativeCoefficientEquiv_symm_coeff (k : ℕ)
    (a : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent ι k → ℂ) (e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent ι k) :
    AddMonoidAlgebra.coeff (((normalizedPolynomialNegativeCoefficientEquiv k).symm a).val) ((NegativeLaurentMonomialExponents.Dolbeault.negativeToPositiveMonomialExponent k e).val) = a e :=
  congrFun ((normalizedPolynomialNegativeCoefficientEquiv k).apply_symm_apply a) e

end

/-! The coefficient equivalence sends each normalized monomial to its original single Laurent weight. -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

attribute [local instance] fullNegativeMonomialExponent_finite

local instance normalizedNegativeWeightDecidable (k : ℕ) : DecidableEq (NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent ι k) :=
  Classical.decEq _

def normalizedPositiveMonomial (k : ℕ) (e : NegativeLaurentMonomialExponents.Dolbeault.positiveMonomialExponent ι k) (c : ℂ) :
    NormalizedHomogeneousPolynomials.Dolbeault.normalizedHomogeneousPolynomials (Finset.univ : Finset ι) k := by
  refine ⟨MvPolynomial.monomial e.val c,
    NormalizedPolynomialSupports.Dolbeault.homogeneousPolynomial_normalized_of_support Finset.univ k _
      (MvPolynomial.isHomogeneous_monomial c e.property.1) ?_⟩
  intro v hv i _
  have he : v = e.val := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hv)
  exact he ▸ e.property.2 i

theorem normalizedPositiveMonomial_coefficients (k : ℕ) (e : NegativeLaurentMonomialExponents.Dolbeault.positiveMonomialExponent ι k) (c : ℂ) :
    normalizedPolynomialPositiveCoefficientEquiv k (normalizedPositiveMonomial k e c) =
      Finsupp.single e c := by
  ext f
  change AddMonoidAlgebra.coeff ((MvPolynomial.monomial e.val c)) (f.val) = (Finsupp.single e c) f
  by_cases h : e = f
  · subst f
    simp [MvPolynomial.coeff_monomial]
  · have hv : e.val ≠ f.val := fun hc => h (Subtype.ext hc)
    simp only [MvPolynomial.coeff_monomial, ite_eq_right hv, Finsupp.single_eq_of_ne (Ne.symm h)]

theorem normalizedPositiveMonomial_negativeCoefficients (k : ℕ)
    (e : NegativeLaurentMonomialExponents.Dolbeault.positiveMonomialExponent ι k) (c : ℂ) :
    normalizedPolynomialNegativeCoefficientEquiv k (normalizedPositiveMonomial k e c) =
      Pi.single (NegativeLaurentMonomialExponents.Dolbeault.negativeLaurentMonomialExponentEquiv k e) c := by
  change Finsupp.linearEquivFunOnFinite ℂ ℂ (NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent ι k)
    ((Finsupp.domLCongr (R := ℂ) (M := ℂ) (NegativeLaurentMonomialExponents.Dolbeault.negativeLaurentMonomialExponentEquiv k))
      (normalizedPolynomialPositiveCoefficientEquiv k (normalizedPositiveMonomial k e c))) = _
  rw [normalizedPositiveMonomial_coefficients, Finsupp.domLCongr_single,
    Finsupp.linearEquivFunOnFinite_single]

def normalizedNegativeMonomial (k : ℕ) (e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent ι k) (c : ℂ) :
    NormalizedHomogeneousPolynomials.Dolbeault.normalizedHomogeneousPolynomials (Finset.univ : Finset ι) k :=
  normalizedPositiveMonomial k (NegativeLaurentMonomialExponents.Dolbeault.negativeToPositiveMonomialExponent k e) c

theorem normalizedNegativeMonomial_coefficients (k : ℕ)
    (e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent ι k) (c : ℂ) :
    normalizedPolynomialNegativeCoefficientEquiv k (normalizedNegativeMonomial k e c) = Pi.single e c := by
  change normalizedPolynomialNegativeCoefficientEquiv k
    (normalizedPositiveMonomial k ((NegativeLaurentMonomialExponents.Dolbeault.negativeLaurentMonomialExponentEquiv k).symm e) c) = _
  rw [normalizedPositiveMonomial_negativeCoefficients, Equiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.Comparison.Betti.NormalizedPolynomialCoefficients.Dolbeault
