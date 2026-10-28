import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.IdealPrimeDescent

/-! # Localization Polynomial Membership -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationPolynomialMembership

noncomputable section

/-! Finite polynomial ideal membership can be spread out from any
multiplicative localization by inverting a single member of its multiplicative set. -/

open _root_.MvPolynomial
open scoped BigOperators

universe u v w t
variable {A : Type u} [CommRing A] {σ : Type v}

theorem finite_polynomialIdeal_membership_localization_descent
    (U : Submonoid A) (T : Type w) [CommRing T] [Algebra A T] [IsLocalization U T]
    {κ : Type t} [Fintype κ] (I : κ → Ideal (MvPolynomial σ A)) (f : κ → MvPolynomial σ A)
    (hf : ∀ i, MvPolynomial.map (algebraMap A T) (f i) ∈ (I i).map (MvPolynomial.map (algebraMap A T))) :
    ∃ s : U, ∀ i, MvPolynomial.map (algebraMap A (Localization.Away s.val)) (f i) ∈
      (I i).map (MvPolynomial.map (algebraMap A (Localization.Away s.val))) := by
  classical
  choose d hd using fun i => (Polynomial.IdealPrimeDescent.polynomial_localization_membership_iff U T (I i) (f i)).mp (hf i)
  let s : U := ∏ i, d i
  refine ⟨s, fun i => ?_⟩
  apply (Polynomial.IdealPrimeDescent.polynomial_localization_membership_iff (Submonoid.powers s.val)
    (Localization.Away s.val) (I i) (f i)).mpr
  refine ⟨⟨s.val, Submonoid.mem_powers s.val⟩, ?_⟩
  have hdiv : (d i).val ∣ s.val := by
    change (d i).val ∣ (∏ j, d j : U).val
    rw [Submonoid.coe_finsetProd]
    exact Finset.dvd_prod_of_mem (fun j => (d j).val) (Finset.mem_univ i)
  obtain ⟨a, ha⟩ := hdiv
  rw [ha, map_mul, mul_right_comm]
  exact (I i).mul_mem_right (C a) (hd i)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationPolynomialMembership
