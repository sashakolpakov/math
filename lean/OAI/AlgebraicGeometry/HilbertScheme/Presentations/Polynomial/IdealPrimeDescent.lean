import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.PrimeLocalization
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal

/-! # Ideal Prime Descent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.IdealPrimeDescent

noncomputable section

/-! Membership of finitely many polynomials in coefficient-extended ideals
descends from a prime localization to one principal neighborhood. -/

open _root_.MvPolynomial
open scoped BigOperators

universe u v w t
variable {A : Type u} [CommRing A] {σ : Type v}

theorem polynomial_localization_membership_iff
    (U : Submonoid A) (T : Type w) [CommRing T] [Algebra A T] [IsLocalization U T]
    (I : Ideal (MvPolynomial σ A)) (f : MvPolynomial σ A) :
    MvPolynomial.map (algebraMap A T) f ∈ I.map (MvPolynomial.map (algebraMap A T)) ↔
      ∃ s : U, C s.val * f ∈ I := by
  let : Algebra (MvPolynomial σ A) (MvPolynomial σ T) := MvPolynomial.algebraMvPolynomial
  change algebraMap (MvPolynomial σ A) (MvPolynomial σ T) f ∈
    I.map (algebraMap (MvPolynomial σ A) (MvPolynomial σ T)) ↔ _
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (U.map (C (σ := σ)))]
  constructor
  · rintro ⟨s, ⟨a, ha, rfl⟩, hf⟩
    exact ⟨⟨a, ha⟩, hf⟩
  · rintro ⟨s, hs⟩
    exact ⟨C s.val, ⟨s.val, s.property, rfl⟩, hs⟩

theorem finite_polynomialIdeal_membership_descent
    (p : Ideal A) [p.IsPrime] {κ : Type t} [Fintype κ]
    (I : κ → Ideal (MvPolynomial σ A)) (f : κ → MvPolynomial σ A)
    (hf : ∀ i, MvPolynomial.map (algebraMap A (Localization.AtPrime p)) (f i) ∈
      (I i).map (MvPolynomial.map (algebraMap A (Localization.AtPrime p)))) :
    ∃ (s : A), s ∉ p ∧ ∀ i,
      MvPolynomial.map (algebraMap A (Localization.Away s)) (f i) ∈
        (I i).map (MvPolynomial.map (algebraMap A (Localization.Away s))) := by
  classical
  choose d hd using fun i =>
    (polynomial_localization_membership_iff p.primeCompl (Localization.AtPrime p) (I i) (f i)).mp (hf i)
  let s : p.primeCompl := ∏ i, d i
  refine ⟨s.val, s.property, fun i => ?_⟩
  apply (polynomial_localization_membership_iff (Submonoid.powers s.val)
    (Localization.Away s.val) (I i) (f i)).mpr
  refine ⟨⟨s.val, Submonoid.mem_powers s.val⟩, ?_⟩
  have hdiv : (d i).val ∣ s.val := by
    change (d i).val ∣ (∏ j, d j : p.primeCompl).val
    rw [Submonoid.coe_finsetProd]
    exact Finset.dvd_prod_of_mem (fun j => (d j).val) (Finset.mem_univ i)
  obtain ⟨a, ha⟩ := hdiv
  rw [ha, map_mul, mul_right_comm]
  exact (I i).mul_mem_right (C a) (hd i)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.IdealPrimeDescent
