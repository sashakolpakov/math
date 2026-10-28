import OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousEntirePolynomial
import OAI.AlgebraicGeometry.Comparison.Betti.NegativeCoefficientVanishing

/-! # Coefficient Polynomials -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Laurent.CoefficientPolynomials.Dolbeault

noncomputable section

/-! The all-positive and all-negative entire Laurent coefficients are ordinary homogeneous polynomials. -/

open _root_.TopologicalSpace

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem positiveCoefficient_exists_polynomial (d : ℕ)
    (a : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset ι) (d : ℤ)) :
    ∃ P : MvPolynomial ι ℂ, P.IsHomogeneous d ∧
      ∀ x : ι → ℂ, MvPolynomial.eval x P = SectorSum.Dolbeault.laurentEntireFunction a.val x := by
  apply HomogeneousEntirePolynomial.Dolbeault.exists_homogeneousPolynomial_of_entire a.val d
  intro c hc x
  have hpoint : FiniteUniqueness.Dolbeault.laurentSectorScale c (∅ : Finset ι) x = c • x := by
    funext i
    simp only [FiniteUniqueness.Dolbeault.laurentSectorScale, Finset.notMem_empty, ite_false, Pi.smul_apply, smul_eq_mul]
  exact (congrArg (SectorSum.Dolbeault.laurentEntireFunction a.val) hpoint).symm.trans
    ((a.property.2 c hc x).trans (by rw [zpow_natCast]))

theorem fullNegativeCoefficient_exists_polynomial_nonpos (d : ℤ) (hd : d ≤ 0)
    (a : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset ι) d) :
    ∃ P : MvPolynomial ι ℂ, P.IsHomogeneous (-d).toNat ∧
      ∀ x : ι → ℂ, MvPolynomial.eval x P = SectorSum.Dolbeault.laurentEntireFunction a.val x := by
  apply HomogeneousEntirePolynomial.Dolbeault.exists_homogeneousPolynomial_of_entire a.val (-d).toNat
  intro c hc x
  have hpoint : FiniteUniqueness.Dolbeault.laurentSectorScale c⁻¹ (Finset.univ : Finset ι) x = c • x := by
    funext i
    simp only [FiniteUniqueness.Dolbeault.laurentSectorScale, Finset.mem_univ, ite_true, inv_inv, Pi.smul_apply, smul_eq_mul]
  have hpower : (c⁻¹) ^ d = c ^ (-d).toNat := by
    rw [inv_zpow, ← zpow_neg, ← Int.toNat_of_nonneg (neg_nonneg.mpr hd), zpow_natCast]
    rfl
  exact (congrArg (SectorSum.Dolbeault.laurentEntireFunction a.val) hpoint).symm.trans
    ((a.property.2 c⁻¹ (inv_ne_zero hc) x).trans (congrArg (· * SectorSum.Dolbeault.laurentEntireFunction a.val x) hpower))

theorem fullNegativeCoefficient_exists_polynomial [Nonempty ι] (d : ℤ)
    (a : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset ι) d) :
    ∃ P : MvPolynomial ι ℂ, P.IsHomogeneous (-d).toNat ∧
      (∀ x : ι → ℂ, MvPolynomial.eval x P = SectorSum.Dolbeault.laurentEntireFunction a.val x) ∧
      ∀ (i : ι) (x : ι → ℂ), x i = 0 → MvPolynomial.eval x P = 0 := by
  have hex : ∃ P : MvPolynomial ι ℂ, P.IsHomogeneous (-d).toNat ∧
      ∀ x : ι → ℂ, MvPolynomial.eval x P = SectorSum.Dolbeault.laurentEntireFunction a.val x := by
    by_cases hd : d ≤ 0
    · exact fullNegativeCoefficient_exists_polynomial_nonpos d hd a
    · have ha := NegativeCoefficientVanishing.Dolbeault.fullNegativeCoefficient_zero_nonneg d (le_of_lt (lt_of_not_ge hd)) a
      refine ⟨0, MvPolynomial.isHomogeneous_zero ι ℂ _, ?_⟩
      intro x
      rw [ha]
      rfl
  obtain ⟨P, hP, he⟩ := hex
  refine ⟨P, hP, he, ?_⟩
  intro i x hx
  exact (he x).trans (a.property.1 i (Finset.mem_univ i) ⟨x, trivial⟩ hx)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Laurent.CoefficientPolynomials.Dolbeault
