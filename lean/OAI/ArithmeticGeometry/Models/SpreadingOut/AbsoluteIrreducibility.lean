import OAI.ArithmeticGeometry.Models.SpreadingOut.FactorizationPoints

/-! # Absolute Irreducibility -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.AbsoluteIrreducibility.Construction

noncomputable section

/-! Absolute irreducibility persists after inverting one nonzero base element.
The proof bounds possible factor coefficients and excludes the corresponding
finite-type parameter algebras by algebraic specialization. -/

open _root_.MvPolynomial
open scoped BigOperators

universe u

open OAI.ArithmeticGeometry.Models.SpreadingOut.FactorizationPoints.Construction.PolynomialFactorization

theorem absolute_irreducibility_after_inverting_nonzero
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {n : ℕ} (p : MvPolynomial (Fin n) R)
    (hp : Irreducible (MvPolynomial.map (algebraMap R (AlgebraicClosure K)) p)) :
    ∃ r : R, r ≠ 0 ∧
      ∀ (k : Type u) [Field k] (φ : R →+* k), φ r ≠ 0 → Irreducible (MvPolynomial.map φ p) := by
  classical
  obtain ⟨m, hm, hcoeff⟩ := BoundedPolynomial.Construction.nonconstant_coefficient_of_nonunit hp.ne_zero hp.not_isUnit
  have ha : p.coeff m ≠ 0 := by
    intro h
    apply hcoeff
    simp only [coeff_map, h, map_zero]
  let W := {w : Fin 2 → BoundedPolynomial.Construction.PolynomialBox n p.totalDegree // ∀ i, BoundedPolynomial.Construction.polynomialBoxExponent (w i) ≠ 0}
  let : Fintype W := Fintype.ofFinite W
  choose r hr using fun w : W ↦ FactorizationPoints.Construction.PolynomialFactorization.parameter_algebra_killed_by_nonzero p w.val w.property hp
  let a : R := p.coeff m * ∏ w : W, r w
  have ha0 : a ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr fun w _ ↦ (hr w).1)
  refine ⟨a, ha0, fun k _ φ hφ ↦ ?_⟩
  let : Algebra R k := φ.toAlgebra
  have hac : φ (p.coeff m) ≠ 0 := by
    apply left_ne_zero_of_mul
    change φ (p.coeff m) * φ (∏ w : W, r w) ≠ 0
    simpa only [a, map_mul] using hφ
  have hrc (w : W) : φ (r w) ≠ 0 := by
    have ht : (∏ w : W, φ (r w)) ≠ 0 := by
      apply right_ne_zero_of_mul
      change φ (p.coeff m) * (∏ w : W, φ (r w)) ≠ 0
      simpa only [a, map_mul, map_prod] using hφ
    exact (Finset.prod_ne_zero_iff.mp ht) w (Finset.mem_univ w)
  have hpc : (MvPolynomial.map φ p).coeff m ≠ 0 := by
    rw [coeff_map]
    exact hac
  have hpn : ¬ IsUnit (MvPolynomial.map φ p) :=
    BoundedPolynomial.Construction.polynomial_not_isUnit_of_nonconstant_coefficient hm hpc
  have hp0 : MvPolynomial.map φ p ≠ 0 := fun h ↦ hpc (by simp only [h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply])
  refine ⟨hpn, fun q₀ q₁ he ↦ ?_⟩
  by_contra hunit
  obtain ⟨hu₀, hu₁⟩ := not_or.mp hunit
  have hq₀ : q₀ ≠ 0 := fun h ↦ hp0 (by simp [he, h])
  have hq₁ : q₁ ≠ 0 := fun h ↦ hp0 (by simp [he, h])
  have hdegree : (MvPolynomial.map φ p).totalDegree ≤ p.totalDegree :=
    Finset.sup_mono (support_map_subset φ p)
  let q : Fin 2 → MvPolynomial (Fin n) k := ![q₀, q₁]
  have hq (i : Fin 2) : (q i).totalDegree ≤ p.totalDegree := by
    fin_cases i
    · exact (totalDegree_le_of_dvd_of_isDomain ⟨q₁, he⟩ hp0).trans hdegree
    · exact (totalDegree_le_of_dvd_of_isDomain ⟨q₀, he.trans (mul_comm _ _)⟩ hp0).trans hdegree
  have hqn (i : Fin 2) : q i ≠ 0 ∧ ¬ IsUnit (q i) := by
    fin_cases i
    · exact ⟨hq₀, hu₀⟩
    · exact ⟨hq₁, hu₁⟩
  choose v hv hvcoeff using fun i ↦ BoundedPolynomial.Construction.nonconstant_coefficient_of_nonunit (hqn i).1 (hqn i).2
  choose w hw using fun i ↦ BoundedPolynomial.Construction.support_in_polynomialBox (q i) (hq i)
    (mem_support_iff.mpr (hvcoeff i))
  let ww : W := ⟨w, fun i ↦ by rw [hw i]; exact hv i⟩
  have hcw (i : Fin 2) : (q i).coeff (BoundedPolynomial.Construction.polynomialBoxExponent (ww.val i)) ≠ 0 := by
    change (q i).coeff (BoundedPolynomial.Construction.polynomialBoxExponent (w i)) ≠ 0
    rw [hw i]
    exact hvcoeff i
  obtain ⟨ψ⟩ := FactorizationPoints.Construction.PolynomialFactorization.nonempty_of_factorization p q ww.val hq he hcw
  have hk := congrArg ψ (hr ww).2
  apply hrc ww
  exact (ψ.commutes (r ww)).symm.trans (hk.trans ψ.map_zero)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.AbsoluteIrreducibility.Construction
