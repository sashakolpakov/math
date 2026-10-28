import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreePolynomial
import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIs
import OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.Quotient

/-! # Degree Integrality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIntegrality

noncomputable section

/-! The geometric degree polynomial has integer coefficients. An actual
integral annihilator of the endomorphism gives divisibility at every
sufficiently large integer. Polynomial division and integrally closedness
then give coefficient integrality, without a cohomological comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Filter

open OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreePolynomial OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIs.Divisibility
  IntegralComparison.Polynomial.Quotient.Integral

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

theorem degree_polynomial_dvd_annihilator_power
    (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (D : Polynomial ℚ) (hD : D.Monic) (b : ℕ)
    (hvalues : ∀ n : ℕ, b ≤ n →
      D.eval (n : ℚ) =
        (((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left.residueDegree
          (genericPoint A.left) : ℚ))
    (Q : Polynomial ℤ) (hQ : Q.Monic) (hQf : Polynomial.aeval f Q = 0) :
    D ∣ (Q.map (Int.castRingHom ℚ)) ^ (2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) := by
  obtain ⟨c, hc⟩ := DegreeIs.Divisibility.shift_degree_eventually_dvd_annihilator A f Q hQ hQf
  apply IntegralComparison.Polynomial.Quotient.Integral.dvd_of_eventual_integral_quotient _ _ hD.ne_zero
  filter_upwards [eventually_ge_atTop (max b c)] with n hn
  obtain ⟨z, hz⟩ := hc n ((le_max_right b c).trans hn)
  refine ⟨z, ?_⟩
  rw [Polynomial.eval_pow, Polynomial.eval_natCast_map,
    hvalues n ((le_max_left b c).trans hn)]
  simpa only [map_pow, map_mul, Int.coe_castRingHom, Int.cast_natCast] using
    congrArg (Int.castRingHom ℚ) hz

theorem exists_monic_integer_degree_polynomial (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    ∃ W : Polynomial ℤ, W.Monic ∧
      W.natDegree = 2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom ∧
      ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
        W.eval (n : ℤ) =
          (((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left.residueDegree
            (genericPoint A.left) : ℤ) := by
  obtain ⟨D, hD, hdegree, b, hvalues⟩ := DegreePolynomial.exists_degree_polynomial_on_tail A f
  let : Module.Finite ℤ (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :=
    Module.Finite.iff_addGroup_fg.mpr (AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.FiniteGeneration.Construction.algebraicEnd_finiteGenerated A)
  obtain ⟨Q, hQ, hQf⟩ := IsIntegral.of_finite ℤ f
  have hdiv := degree_polynomial_dvd_annihilator_power A f D hD b hvalues Q hQ hQf
  obtain ⟨W, hW, hWD⟩ := IntegralComparison.Polynomial.Quotient.Integral.exists_monic_integer_of_dvd_monic D hD
    (Q ^ (2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom))
    (hQ.pow _) (by simpa only [Polynomial.map_pow] using hdiv)
  refine ⟨W, hW, ?_, b, ?_⟩
  · calc
      W.natDegree = (W.map (Int.castRingHom ℚ)).natDegree :=
        (Polynomial.natDegree_map_eq_of_injective (Int.cast_injective (α := ℚ)) W).symm
      _ = 2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom := by rw [hWD]; exact hdegree
  · intro n hn
    apply Int.cast_injective (α := ℚ)
    have hv := hvalues n hn
    rw [← hWD, Polynomial.eval_natCast_map] at hv
    simpa only [Int.coe_castRingHom, Int.cast_natCast] using hv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIntegrality
