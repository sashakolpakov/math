import OAI.AlgebraicGeometry.Comparison.Betti.NormalizedPolynomialCoefficients
import OAI.AlgebraicGeometry.Comparison.Betti.NegativePolynomialCoefficientEquiv

/-! # Analytic Negative Coefficients -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.AnalyticNegativeCoefficients.Dolbeault

noncomputable section

/-! The analytic full-negative sector uses exactly the original algebraic Laurent coefficient space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def negativeAnalyticLaurentCoefficientEquiv (N k : ℕ) :
    HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin N)) (-(k : ℤ)) ≃ₗ[ℂ]
      (NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k → ℂ) :=
  (NegativePolynomialCoefficientEquiv.Dolbeault.negativePolynomialCoefficientEquiv N k).symm.trans
    (NormalizedPolynomialCoefficients.Dolbeault.normalizedPolynomialNegativeCoefficientEquiv k)

theorem negativeAnalyticLaurentCoefficientEquiv_polynomial (N k : ℕ)
    (P : NormalizedHomogeneousPolynomials.Dolbeault.normalizedHomogeneousPolynomials (Finset.univ : Finset (Fin N)) k)
    (e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k) :
    negativeAnalyticLaurentCoefficientEquiv N k (NegativePolynomialCoefficientEquiv.Dolbeault.negativePolynomialCoefficientEquiv N k P) e =
      AddMonoidAlgebra.coeff (P.val) ((NegativeLaurentMonomialExponents.Dolbeault.negativeToPositiveMonomialExponent k e).val) := by
  change NormalizedPolynomialCoefficients.Dolbeault.normalizedPolynomialNegativeCoefficientEquiv k
    ((NegativePolynomialCoefficientEquiv.Dolbeault.negativePolynomialCoefficientEquiv N k).symm (NegativePolynomialCoefficientEquiv.Dolbeault.negativePolynomialCoefficientEquiv N k P)) e = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

def algebraicNegativeLaurentCoefficientEquiv (N k : ℕ) :
    (NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k → Γ(Spec (CommRingCat.of ℂ), ⊤)) ≃+
      HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin N)) (-(k : ℤ)) :=
  (AddEquiv.piCongrRight fun _ =>
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.toAddEquiv).trans
      (negativeAnalyticLaurentCoefficientEquiv N k).symm.toAddEquiv

theorem algebraicNegativeLaurentCoefficientEquiv_coefficient (N k : ℕ)
    (a : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k → Γ(Spec (CommRingCat.of ℂ), ⊤))
    (e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k) :
    negativeAnalyticLaurentCoefficientEquiv N k (algebraicNegativeLaurentCoefficientEquiv N k a) e =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (a e) :=
  congrFun ((negativeAnalyticLaurentCoefficientEquiv N k).apply_symm_apply
    (fun e => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (a e))) e

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.AnalyticNegativeCoefficients.Dolbeault
