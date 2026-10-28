import OAI.AlgebraicGeometry.Comparison.Betti.PositiveLaurentPolynomialCoefficients
import OAI.AlgebraicGeometry.Comparison.Betti.NormalizedHomogeneousPolynomials

/-! # Positive Analytic Monomial -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PositiveAnalyticMonomial.Dolbeault

noncomputable section

section

/-! Original nonnegative Laurent coefficients identify normalized analytic polynomial monomials. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open scoped BigOperators

local instance (N k : ℕ) : DecidableEq (SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin N) (k : ℤ)) := Classical.decEq _

def positiveAnalyticLaurentCoefficientEquiv (N k : ℕ) :
    HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin N)) (k : ℤ) ≃ₗ[ℂ]
      (SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin N) (k : ℤ) → ℂ) :=
  (NormalizedHomogeneousPolynomials.Dolbeault.positivePolynomialCoefficientEquiv N k).symm.trans
    (SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv ℂ k)

def algebraicPositiveLaurentCoefficientEquiv (N k : ℕ) :
    (SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin N) (k : ℤ) → Γ(Spec (CommRingCat.of ℂ), ⊤)) ≃+
      HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin N)) (k : ℤ) :=
  (AddEquiv.piCongrRight fun _ =>
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.toAddEquiv).trans
      (positiveAnalyticLaurentCoefficientEquiv N k).symm.toAddEquiv

theorem algebraicPositiveLaurentCoefficientEquiv_coefficient (N k : ℕ)
    (a : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin N) (k : ℤ) → Γ(Spec (CommRingCat.of ℂ), ⊤))
    (e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin N) (k : ℤ)) :
    positiveAnalyticLaurentCoefficientEquiv N k (algebraicPositiveLaurentCoefficientEquiv N k a) e =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (a e) :=
  congrFun ((positiveAnalyticLaurentCoefficientEquiv N k).apply_symm_apply
    (fun e => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (a e))) e

def positiveAnalyticMonomial (N k : ℕ) (e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin N) (k : ℤ)) (c : ℂ) :
    HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin N)) (k : ℤ) :=
  NormalizedHomogeneousPolynomials.Dolbeault.positivePolynomialCoefficientEquiv N k (PositiveLaurentPolynomialCoefficients.Dolbeault.positiveLaurentPolynomialMonomial N k e c)

theorem positiveAnalyticMonomial_coefficients (N k : ℕ)
    (e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin N) (k : ℤ)) (c : ℂ) :
    positiveAnalyticLaurentCoefficientEquiv N k (positiveAnalyticMonomial N k e c) = Pi.single e c := by
  change SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv ℂ k
    ((NormalizedHomogeneousPolynomials.Dolbeault.positivePolynomialCoefficientEquiv N k).symm
      (NormalizedHomogeneousPolynomials.Dolbeault.positivePolynomialCoefficientEquiv N k (PositiveLaurentPolynomialCoefficients.Dolbeault.positiveLaurentPolynomialMonomial N k e c))) = _
  rw [LinearEquiv.symm_apply_apply, PositiveLaurentPolynomialCoefficients.Dolbeault.positiveLaurentPolynomialMonomial_coefficients]

theorem positiveAnalyticMonomial_apply (N k : ℕ)
    (e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin N) (k : ℤ)) (c : ℂ) (x : Fin N → ℂ) :
    Laurent.SectorSum.Dolbeault.laurentEntireFunction (positiveAnalyticMonomial N k e c).val x = c * ∏ i, x i ^ e.val.val i := by
  change MvPolynomial.eval x (MvPolynomial.monomial (SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree k e).val c) = _
  rw [MvPolynomial.eval_monomial, Finsupp.prod_pow]
  apply congrArg (c * ·)
  apply Finset.prod_congr rfl
  intro i _
  change x i ^ (e.val.val i).toNat = x i ^ e.val.val i
  rw [← zpow_natCast, Int.toNat_of_nonneg (e.property i)]

theorem positiveAnalyticMonomial_inverse_apply (N k : ℕ)
    (e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin N) (k : ℤ)) (c : ℂ) (x : Fin N → ℂ) :
    Laurent.SectorSum.Dolbeault.laurentEntireFunction (positiveAnalyticMonomial N k e c).val (Laurent.SectorTo.Dolbeault.laurentInverseCoordinates ∅ x) =
      c * ∏ i, x i ^ e.val.val i := by
  have hx : Laurent.SectorTo.Dolbeault.laurentInverseCoordinates (∅ : Finset (Fin N)) x = x := by
    funext i
    simp only [Laurent.SectorTo.Dolbeault.laurentInverseCoordinates, Finset.notMem_empty, ite_false]
  rw [hx, positiveAnalyticMonomial_apply]

end

/-! Actual empty-sector homogeneous coefficients have the finite original nonnegative Laurent expansion. -/

open _root_.MvPolynomial
open scoped BigOperators

local instance (N k : ℕ) : DecidableEq (SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin N) (k : ℤ)) := Classical.decEq _

local instance (N k : ℕ) : AddCommGroup ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin N)) (k : ℤ)) :=
  Submodule.addCommGroup _

theorem positiveAnalyticCoefficient_expansion (N k : ℕ)
    (a : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin N)) (k : ℤ)) :
    (∑ e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin N) (k : ℤ),
      positiveAnalyticMonomial N k e (positiveAnalyticLaurentCoefficientEquiv N k a e)) = a := by
  apply (positiveAnalyticLaurentCoefficientEquiv N k).injective
  have hs := map_sum (positiveAnalyticLaurentCoefficientEquiv N k).toAddEquiv.toAddMonoidHom
    (fun e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin N) (k : ℤ) =>
      positiveAnalyticMonomial N k e (positiveAnalyticLaurentCoefficientEquiv N k a e)) Finset.univ
  refine hs.trans ?_
  exact (Finset.sum_congr rfl (fun e _ => positiveAnalyticMonomial_coefficients N k e
    (positiveAnalyticLaurentCoefficientEquiv N k a e))).trans
      (Finset.univ_sum_single (positiveAnalyticLaurentCoefficientEquiv N k a))

end

end OAI.AlgebraicGeometry.Comparison.Betti.PositiveAnalyticMonomial.Dolbeault
