import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Data.Finsupp.Fintype

/-! # Bounded Polynomial -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.BoundedPolynomial.Construction

noncomputable section

/-! Finite coefficient coordinates for polynomials of bounded degree. -/

open _root_.MvPolynomial
open scoped BigOperators

universe u

abbrev PolynomialBox (n d : ℕ) := Fin n → Fin (d + 1)

def polynomialBoxExponent {n d : ℕ} (a : PolynomialBox n d) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i ↦ (a i).val)

theorem polynomialBoxExponent_injective {n d : ℕ} :
    Function.Injective (@polynomialBoxExponent n d) := by
  intro a b h
  funext i
  apply Fin.ext
  exact congrArg (fun f : Fin n →₀ ℕ ↦ f i) h

@[simp]
theorem polynomialBoxExponent_eq_iff {n d : ℕ} (a b : PolynomialBox n d) :
    polynomialBoxExponent a = polynomialBoxExponent b ↔ a = b :=
  polynomialBoxExponent_injective.eq_iff

def boundedPolynomial {R : Type u} [CommSemiring R] {n d : ℕ}
    (a : PolynomialBox n d → R) : MvPolynomial (Fin n) R :=
  ∑ v, monomial (polynomialBoxExponent v) (a v)

theorem boundedPolynomial_coeff {R : Type u} [CommSemiring R] {n d : ℕ}
    (a : PolynomialBox n d → R) (v : PolynomialBox n d) :
    (boundedPolynomial a).coeff (polynomialBoxExponent v) = a v := by
  classical
  simp [boundedPolynomial, coeff_monomial]

theorem boundedPolynomial_map {R S : Type u} [CommSemiring R] [CommSemiring S]
    {n d : ℕ} (a : PolynomialBox n d → R) (f : R →+* S) :
    MvPolynomial.map f (boundedPolynomial a) = boundedPolynomial (fun v ↦ f (a v)) := by
  simp [boundedPolynomial]

theorem support_in_polynomialBox {R : Type u} [CommSemiring R] {n d : ℕ}
    (p : MvPolynomial (Fin n) R) (hp : p.totalDegree ≤ d)
    {m : Fin n →₀ ℕ} (hm : m ∈ p.support) :
    ∃ v : PolynomialBox n d, polynomialBoxExponent v = m := by
  let v : PolynomialBox n d := fun i ↦ ⟨m i,
    Nat.lt_succ_of_le ((le_degreeOf_of_mem_support i hm).trans ((degreeOf_le_totalDegree p i).trans hp))⟩
  exact ⟨v, by ext; rfl⟩

theorem boundedPolynomial_reconstruct {R : Type u} [CommSemiring R] {n d : ℕ}
    (p : MvPolynomial (Fin n) R) (hp : p.totalDegree ≤ d) :
    boundedPolynomial (fun v : PolynomialBox n d ↦ p.coeff (polynomialBoxExponent v)) = p := by
  classical
  ext m
  by_cases hm : ∃ v : PolynomialBox n d, polynomialBoxExponent v = m
  · obtain ⟨v, rfl⟩ := hm
    exact boundedPolynomial_coeff _ v
  · have hm' : m ∉ p.support := fun h ↦ hm (support_in_polynomialBox p hp h)
    have hcoeff : p.coeff m = 0 := notMem_support_iff.mp hm'
    rw [hcoeff]
    have hne (v : PolynomialBox n d) : polynomialBoxExponent v ≠ m := fun h ↦ hm ⟨v, h⟩
    simp [boundedPolynomial, coeff_monomial, hne]

theorem polynomial_not_isUnit_of_nonconstant_coefficient
    {k : Type u} [Field k] {n : ℕ} {p : MvPolynomial (Fin n) k}
    {m : Fin n →₀ ℕ} (hm : m ≠ 0) (hc : p.coeff m ≠ 0) : ¬ IsUnit p := by
  intro h
  exact hc (isNilpotent_iff_eq_zero.mp ((MvPolynomial.isUnit_iff.mp h).2 m hm))

theorem nonconstant_coefficient_of_nonunit
    {k : Type u} [Field k] {n : ℕ} {p : MvPolynomial (Fin n) k}
    (hp : p ≠ 0) (hu : ¬ IsUnit p) :
    ∃ m : Fin n →₀ ℕ, m ≠ 0 ∧ p.coeff m ≠ 0 := by
  classical
  by_contra h
  have hc (m : Fin n →₀ ℕ) (hm : m ≠ 0) : p.coeff m = 0 := by
    by_contra hc
    exact h ⟨m, hm, hc⟩
  have he : p = C (p.coeff 0) := by
    ext m
    by_cases hm : m = 0
    · subst m; simp
    · simp [coeff_C, Ne.symm hm, hc m hm]
  have hzero : p.coeff 0 ≠ 0 := fun h ↦ hp (by simpa [h] using he)
  exact hu (MvPolynomial.isUnit_iff_eq_C_of_isReduced.mpr
    ⟨p.coeff 0, isUnit_iff_ne_zero.mpr hzero, he⟩)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.BoundedPolynomial.Construction
