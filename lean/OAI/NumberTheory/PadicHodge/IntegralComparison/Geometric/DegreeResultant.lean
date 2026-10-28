import OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantPolynomialResultant

/-! # Degree Resultant -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.DegreeResultant

noncomputable section

/-! The actual geometric degree polynomial determines degrees of
polynomials in the endomorphism by a genuine resultant identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeShift.Law OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantPolynomialResultant

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

def integerPolynomial (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) : Polynomial ℤ :=
  (IntegralComparison.Polynomial.DegreeShift.Law.exists_integer_shiftPolynomial A F).choose

theorem integerPolynomial_monic (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) : (integerPolynomial A F).Monic :=
  (IntegralComparison.Polynomial.DegreeShift.Law.exists_integer_shiftPolynomial A F).choose_spec.1

theorem integerPolynomial_natDegree (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    (integerPolynomial A F).natDegree = 2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom :=
  (IntegralComparison.Polynomial.DegreeShift.Law.exists_integer_shiftPolynomial A F).choose_spec.2.1

theorem integerPolynomial_map (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    (integerPolynomial A F).map (Int.castRingHom ℚ) = IntegralComparison.Polynomial.DegreeShift.Law.shiftPolynomial A F :=
  (IntegralComparison.Polynomial.DegreeShift.Law.exists_integer_shiftPolynomial A F).choose_spec.2.2.symm

theorem resultant_eq_norm_of_splits (L : Type*) [Field L] [Algebra ℚ L]
    (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (R : Polynomial L) (hR : R.Splits) :
    ((integerPolynomial A F).map (Int.castRingHom L)).resultant R = IntegralComparison.Polynomial.DegreeBaseChange.Law.norm A L F R := by
  let W := (integerPolynomial A F).map (Int.castRingHom L)
  have hW : W.Monic := (integerPolynomial_monic A F).map _
  have hd : W.natDegree = 2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom :=
    ((integerPolynomial_monic A F).natDegree_map _).trans (integerPolynomial_natDegree A F)
  have hm : (IntegralComparison.Polynomial.DegreeShift.Law.shiftPolynomial A F).map (algebraMap ℚ L) = W := by
    rw [← integerPolynomial_map, Polynomial.map_map]
    congr 1
    ext z
    simp
  have h := DeterminantPolynomialResultant.resultant_eq_multiplicative_eval (IntegralComparison.Polynomial.DegreeBaseChange.Law.normHom A L F) Polynomial.X W hW
    (fun c => by
      change IntegralComparison.Polynomial.DegreeBaseChange.Law.norm A L F (Polynomial.C c) = c ^ W.natDegree
      rw [hd, IntegralComparison.Polynomial.DegreeScalars.Law.norm_C])
    (fun c => by
      rw [← hm, Polynomial.eval_map]
      exact IntegralComparison.Polynomial.DegreeShift.Law.shiftPolynomial_aeval A L F c) R hR
  simpa only [Polynomial.aeval_X_left_apply, IntegralComparison.Polynomial.DegreeBaseChange.Law.normHom,
    MonoidHom.coe_mk, OneHom.coe_mk, W] using h

theorem resultant_eq_norm (L : Type*) [Field L] [Algebra ℚ L]
    (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (R : Polynomial L) :
    ((integerPolynomial A F).map (Int.castRingHom L)).resultant R = IntegralComparison.Polynomial.DegreeBaseChange.Law.norm A L F R := by
  let M := AlgebraicClosure L
  let φ : L →ₐ[ℚ] M := IsScalarTower.toAlgHom ℚ L M
  apply (algebraMap L M).injective
  have h := resultant_eq_norm_of_splits A M F (R.map (algebraMap L M)) (IsAlgClosed.splits _)
  have hm : (integerPolynomial A F).map (Int.castRingHom M) =
      ((integerPolynomial A F).map (Int.castRingHom L)).map (algebraMap L M) := by
    rw [Polynomial.map_map]
    congr 1
  rw [hm, Polynomial.natDegree_map_eq_of_injective (algebraMap L M).injective,
    Polynomial.natDegree_map_eq_of_injective (algebraMap L M).injective,
    Polynomial.resultant_map_map] at h
  have hn := IntegralComparison.Polynomial.DegreeBaseChange.Law.norm_map A L M F φ R
  change IntegralComparison.Polynomial.DegreeBaseChange.Law.norm A M F (R.map (algebraMap L M)) = (algebraMap L M) (IntegralComparison.Polynomial.DegreeBaseChange.Law.norm A L F R) at hn
  exact h.trans hn

theorem resultant_eq_residueDegree (L : Type*) [Field L] [Algebra ℚ L]
    (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (R : Polynomial ℕ)
    [IsFinite (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A F R).toMul.hom.hom.left]
    [IsDominant (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A F R).toMul.hom.hom.left] :
    ((integerPolynomial A F).map (Int.castRingHom L)).resultant (R.map (Nat.castRingHom L)) =
      ((IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A F R).toMul.hom.hom.left.residueDegree (genericPoint A.left) : L) := by
  rw [resultant_eq_norm, IntegralComparison.Polynomial.DegreeGeometry.Law.norm_map_nat]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.DegreeResultant
