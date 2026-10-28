import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.Cone

/-! # Rees Coefficients -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ReesCoefficients.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the coefficient ideal of the normal cone

The extension of I to R[It] consists exactly of Rees polynomials whose
degree-n coefficient lies in I^(n+1). This identifies the relations in the
normal-cone presentation without any finite-generation assumption on I.
-/

open _root_.Polynomial
open scoped BigOperators

universe u
variable {R : Type u} [CommRing R]

/-- Rees polynomials with one extra power of I in every coefficient. -/
def reesCoefficientIdeal (I : Ideal R) : Ideal (reesAlgebra I) where
  carrier := {p | ∀ n, p.val.coeff n ∈ I ^ (n + 1)}
  zero_mem' _ := Ideal.zero_mem _
  add_mem' hp hq n := Ideal.add_mem _ (hp n) (hq n)
  smul_mem' s p hp n := by
    change (s.val * p.val).coeff n ∈ _
    rw [coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨j, k⟩ hjk
    have h := Ideal.mul_mem_mul (s.property j) (hp k)
    rw [← pow_add] at h
    convert h using 1
    exact congrArg (fun m => I ^ m) (by have := Finset.mem_antidiagonal.mp hjk; omega)

theorem normalConeIdeal_le_reesCoefficientIdeal (I : Ideal R) :
    Normal.Cone.BundleCycles.normalConeIdeal I ≤ reesCoefficientIdeal I := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro r hr n
  change (C r).coeff n ∈ I ^ (n + 1)
  rw [coeff_C]
  split_ifs with hn
  · simpa [hn] using hr
  · exact Ideal.zero_mem _

/-- Each coefficient in I^(n+1) is a finite sum of products of a coefficient
in I with a degree-n Rees monomial. -/
theorem normalConeIdeal_contains_monomial (I : Ideal R) (n : ℕ) (r : R)
    (hr : r ∈ I ^ (n + 1)) :
    ∃ p : reesAlgebra I, p ∈ Normal.Cone.BundleCycles.normalConeIdeal I ∧ p.val = monomial n r := by
  rw [pow_succ'] at hr
  refine Submodule.smul_induction_on hr ?_ ?_
  · intro a ha b hb
    let p : reesAlgebra I := ⟨monomial n b, reesAlgebra.monomial_mem.mpr hb⟩
    refine ⟨algebraMap R (reesAlgebra I) a * p,
      Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha), ?_⟩
    change C a * monomial n b = monomial n (a * b)
    simp only [C_mul_monomial]
  · intro a b ha hb
    obtain ⟨p, hp, ep⟩ := ha
    obtain ⟨q, hq, eq⟩ := hb
    refine ⟨p + q, Ideal.add_mem _ hp hq, ?_⟩
    change p.val + q.val = _
    rw [ep, eq, map_add]

/-- Exact coefficient description of the ideal defining the normal cone. -/
theorem normalConeIdeal_eq_reesCoefficientIdeal (I : Ideal R) :
    Normal.Cone.BundleCycles.normalConeIdeal I = reesCoefficientIdeal I := by
  classical
  apply le_antisymm (normalConeIdeal_le_reesCoefficientIdeal I)
  intro p hp
  have hm (n : ℕ) := normalConeIdeal_contains_monomial I n (p.val.coeff n) (hp n)
  choose q hq eq using hm
  have he : p = ∑ n ∈ p.val.support, q n := by
    apply Subtype.ext
    change p.val = (reesAlgebra I).val (∑ n ∈ p.val.support, q n)
    simp only [map_sum]
    change p.val = ∑ n ∈ p.val.support, (q n).val
    simp only [eq]
    exact p.val.as_sum_support
  rw [he]
  exact Ideal.sum_mem _ fun n hn => hq n

theorem mem_normalConeIdeal_iff (I : Ideal R) (p : reesAlgebra I) :
    p ∈ Normal.Cone.BundleCycles.normalConeIdeal I ↔ ∀ n, p.val.coeff n ∈ I ^ (n + 1) := by
  rw [normalConeIdeal_eq_reesCoefficientIdeal]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ReesCoefficients.BundleCycles
