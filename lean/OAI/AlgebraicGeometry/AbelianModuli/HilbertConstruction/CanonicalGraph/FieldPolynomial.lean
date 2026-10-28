import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.FieldEulerFormula
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.PolynomialUniqueness

/-! # Field Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over every field, the original graph bundle has a positive Euler coefficient and a monomial section Hilbert polynomial of exact degree g. The polarization-type evaluation of that coefficient remains separate. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_euler_pos_overField (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    0 < CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf := by
  obtain ⟨E⟩ := A.graphBundle_isAmple_overField.exists_powerProjectiveEmbedding
    A.abelian.scheme.hom
  have hp := A.graphBundle_embeddedPower_euler_pos hN hNk E
  rw [A.graphBundle_positivePower_euler_overField hN hNk E.degree E.degree_pos] at hp
  have hpow : 0 ≤ (E.degree : ℤ) ^ g := pow_nonneg (Int.natCast_nonneg _) _
  nlinarith

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_monomial_hilbertPolynomial_overField
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    A.graphBundle.HasSectionHilbertPolynomial A.abelian.scheme.hom
      (Polynomial.monomial g (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom
        A.graphBundle.sheaf : ℚ)) := by
  have hunit : IsUnit (N : Γ(Spec (.of K), ⊤)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr hNk).map (Coefficient.ModulePresheaf.schemeCoefficientMap (𝟙 (Spec (.of K))))
  refine ⟨1, fun m hm => ⟨A.graphBundle_positivePower_sections_finite_overField m, ?_⟩⟩
  rw [Polynomial.eval_monomial]
  have he := congrArg (fun z : ℤ => (z : ℚ))
    (A.graphBundle_tensorPower_euler_overField hN hNk m)
  have hs := congrArg (fun z : ℤ => (z : ℚ))
    (A.graphBundle_positivePower_euler_eq_sections hN hunit m hm)
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] at he hs
  exact he.symm.trans hs

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_hilbertPolynomial_degree_overField
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (P : Polynomial ℚ)
    (hP : A.graphBundle.HasSectionHilbertPolynomial A.abelian.scheme.hom P) :
    P.natDegree = g := by
  have he := A.graphBundle.sectionHilbertPolynomial_unique A.abelian.scheme.hom
    hP (A.graphBundle_monomial_hilbertPolynomial_overField hN hNk)
  rw [he]
  apply Polynomial.natDegree_monomial_eq
  exact Int.cast_ne_zero.mpr (ne_of_gt (A.graphBundle_euler_pos_overField hN hNk))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
