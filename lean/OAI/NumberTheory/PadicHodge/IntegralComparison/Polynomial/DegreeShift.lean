import OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeGeometry
import OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIntegrality

/-! # Degree Shift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeShift.Law

noncomputable section

/-! Integral scalar-shift polynomials of the actual geometric degree
law. The sign conversion is proved using multiplication by -1 in the
polynomial algebra, whose degree is one because 2g is even. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

theorem exists_integer_plusPolynomial (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    ∃ W : Polynomial ℤ, W.Monic ∧
      W.natDegree = 2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom ∧
      DegreeBaseChange.Law.plusPolynomial A F = W.map (Int.castRingHom ℚ) := by
  obtain ⟨W, hW, hd, b, hb⟩ :=
    Endomorphism.DegreeIntegrality.exists_monic_integer_degree_polynomial A (-F)
  refine ⟨W, hW, hd, ?_⟩
  obtain ⟨c, hc⟩ := Frobenius.ShiftIsogeny.endomorphism_shift_eventually_isogeny A (-F)
  apply AlgebraicGeometry.SheafCohomology.Projective.EventualPolynomialIdentity.Dimension.polynomial_eq_of_eventually_nat_eval_eq _ _ (max b c)
  intro n hn
  obtain ⟨hf, hs, _⟩ := hc n ((le_max_right b c).trans hn)
  let R : Polynomial ℕ := Polynomial.C n + Polynomial.X
  have he : DegreeGeometry.Law.naturalEnd A F R = (n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - -F := by
    simp only [DegreeGeometry.Law.naturalEnd, R, Polynomial.eval₂_add, Polynomial.eval₂_C,
      Polynomial.eval₂_X, sub_neg_eq_add]
    rfl
  have : IsFinite (DegreeGeometry.Law.naturalEnd A F R).toMul.hom.hom.left := he.symm ▸ hf
  have : Surjective (DegreeGeometry.Law.naturalEnd A F R).toMul.hom.hom.left := he.symm ▸ hs
  have h := DegreeBaseChange.Law.plusPolynomial_aeval A ℚ F (n : ℚ)
  rw [Polynomial.coe_aeval_eq_eval] at h
  have hm : R.map (Nat.castRingHom ℚ) = Polynomial.C (n : ℚ) + Polynomial.X := by
    simp only [R, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X]
    rfl
  rw [← hm, DegreeGeometry.Law.norm_map_nat A ℚ F R, he] at h
  rw [h, Polynomial.eval_natCast_map, hb n ((le_max_left b c).trans hn)]
  norm_cast

def shiftPolynomial (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) : Polynomial ℚ :=
  (DegreeBaseChange.Law.plusPolynomial A F).comp (-Polynomial.X)

theorem shiftPolynomial_aeval (L : Type*) [CommRing L] [Algebra ℚ L]
    (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (c : L) :
    Polynomial.aeval c (shiftPolynomial A F) =
      DegreeBaseChange.Law.norm A L F (Polynomial.C c - Polynomial.X) := by
  rw [shiftPolynomial, Polynomial.aeval_comp, map_neg, Polynomial.aeval_X,
    DegreeBaseChange.Law.plusPolynomial_aeval]
  have he : (Polynomial.C c - Polynomial.X : Polynomial L) =
      Polynomial.C (-1) * (Polynomial.C (-c) + Polynomial.X) := by
    simp only [map_neg, map_one]
    ring
  rw [he, DegreeBaseChange.Law.norm_mul, DegreeScalars.Law.norm_C]
  have hsign : (-1 : L) ^ (2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) = 1 := by
    rw [pow_mul]
    simp
  rw [hsign, one_mul]

theorem exists_integer_shiftPolynomial (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    ∃ W : Polynomial ℤ, W.Monic ∧
      W.natDegree = 2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom ∧
      shiftPolynomial A F = W.map (Int.castRingHom ℚ) := by
  obtain ⟨W, hW, hd, hp⟩ := exists_integer_plusPolynomial A F
  refine ⟨W.comp (-Polynomial.X), ?_, ?_, ?_⟩
  · change (W.comp (-Polynomial.X)).leadingCoeff = 1
    rw [Polynomial.comp_neg_X_leadingCoeff_eq, hW.leadingCoeff, hd, pow_mul]
    simp
  · simp only [Polynomial.natDegree_comp, Polynomial.natDegree_neg, Polynomial.natDegree_X,
      mul_one, hd]
  · simp only [shiftPolynomial, hp, Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeShift.Law
